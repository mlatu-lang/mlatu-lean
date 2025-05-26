import MlatuLean.Mlatu

open Mlatu

section simplifying_reductions

assert/1 +- = .
assert/2 ~~ = .
assert/1 >< = .
assert/1 +~ = + .
assert/1 >- = - .
assert/2 ,- = - - .
assert/1 +>~ = >+< .
assert/2 >~- = ~-> .
assert/2 ~- - = - - .
assert/2 ~,- = ,- .
assert/1 + > ~ > = >+ .
assert/1 >+<> = >+ .
assert/2 >,<< = ,< .
assert/2 ~ = >(->)(-)(>,>,+,<->,<)+,< .

end simplifying_reductions

section kerby_combinators

def m/1 = +<.
assert (a) m = (a) a.

def rep/1 = +,<.
assert (a) rep = a a.

def rep3/1 = ++,,<.
assert (a) rep3 = a a a.

def run/1 = +>,< .
assert (a) run = a (a).

def z/2 = -< .
assert (b) (a) z = b.

def t/2 = ~<.
assert (b) (a) t = (a) b.

def nip/2 = ~- .

def swat/2 = ~, .

def tack/2 = >,.

def hop/2 = ~> .
assert (b) (a) hop = (a) ((b)).

def baba/2 = ,+ .
assert (b) (a) baba = (b a) (b a).

def sap/2 = ~,< .
assert (b)(a) sap = a b.

def k/2 = ~-< .
assert (b)(a) k = a.

def take/2 = ~>, .
assert (b)(a) take = (a(b)).

def dip/2 = ~>,< .
assert (b)(a) dip = a (b).

def cons/2 = ~>~, .
assert (b)(a) cons = ((b) a).

def twee/2 = ~,>+ .
assert (b)(a) twee = ((a b)) ((a b)).

def cwud/3 = ,~>+ .
assert (c)(b)(a) cwud = (b a)((c))((c)).

def w/2 = (+)~,< .
assert (b)(a) w = (b)(b) a.

def w_parenless/2 = ~>+,~,< .
assert (b)(a) w_parenless = (b)(b) a.

def c/2 = (~)~,< .
assert (z)(y)(x) c = (y)(z)x.
def c_parenless/3 = >~>~,~>,<~<.
assert (z)(y)(x) c_parenless = (y)(z)x.

def poke/3 = >~ >,~-< .
assert (c)(b)(a) poke = (a)(b).

def peek/2 = >(+)~,<~ .
def peek_parenless/2 = >~ >+,~,<~ .
assert (b)(a) peek = (b)(a)(b).
assert (b)(a) peek_parenless = (b)(a)(b).

def dig/2 = (~)~>,<~ .
assert (c)(b)(a) dig = (b)(a)(c).
def dig_parenless/2 =  >~>~,~>,< .
assert (c)(b)(a) dig_parenless = (b)(a)(c).

def bury/3 = ~(~)~>,< .
assert (c)(b)(a) bury = (a)(c)(b).
def bury_parenless/3 = >~ >,~ >,<~ .
assert (c)(b)(a) bury_parenless = (a)(c)(b).

def flip/3 = ~(~)~>,<~ .
assert (c)(b)(a) flip = (a)(b)(c).
def flip_parenless/3 = >~ >,~ >,< .
assert (c)(b)(a) flip_parenless = (a)(b)(c).

def b/3 = (~>~,)~,< .
assert (z)(y)(x) b = ((z)y)x.
def b_parenless/3 = >~>,~>,<>~,~< .
assert (z)(y)(x) b_parenless = ((z)y)x.

def sip/2 = >(+)~,<~>,<.
assert (b)(a) sip = (b)a(b).
def sip_parenless/2 = >~>+,~,<~ >,<.
assert (b)(a) sip_parenless = (b)a(b).

def cake/2 = >~>,+(>~,),~(>,),,< .
assert (b)(a) cake = ((b)a)(a(b)).
def cake_parenless/2 = >~>>,+<~,~<,.
assert (b)(a) cake_parenless = ((b)a)(a(b)).

def s/3 = ((+>)~ >,<,~)~,<.
assert (c)(b)(a) s = ((c) b)(c) a.
def s_parenless/3 = >~>,~>,<>>+,~ >,<,>~,~,<.
assert (c)(b)(a) s_parenless = ((c) b)(c) a.

def j/4 = +>(>~>,)~,(~>~,)~(,),>,<~,<.
assert (d)(c)(b)(a) j = ((c)(d)a)(b)a.
def j_parenless/4 = >+>~,~>,<>~,>~,~ >>,~>>,<,~,~<.
assert (d)(c)(b)(a) j_parenless = ((c)(d)a)(b)a.

def s'/4 = (~,)~,>(~ >+)~,(~,<),~,<.
assert (d)(c)(b)(a) s' = ((d) c) a (d) b.
def s'_parenless/4 = ~ >,>~>,~>>+,~>,<~>,<~,>~,~,<~<.
assert (d)(c)(b)(a) s'_parenless = ((d) c) a (d) b.

def j'/5 = ~(~( ~ >~,~ >,)~ >,<)~ >,<+(~(,)~ >,<)~,<.
assert (e)(d)(c)(b)(a) j' = ((d) a (e) b)(c) b.

end kerby_combinators

namespace z_hop_baba
  def i/1 = () z.
  assert/1 i = <.

  def swap/2 = hop i.
  assert/2 swap = ~.

  def zap/1 = () swap z.
  assert/1 zap = -.

  def unit/1 = () hop hop zap.
  assert/1 unit = >.

  def dup/1 = () baba.
  assert/1 dup = +.

  def cat/2 = baba zap.
  assert/2 cat = ,.
end z_hop_baba

namespace twee_z
  def i/1  = () z.
  assert/1 i = <.

  def unit/1 = () twee (()) twee z i z.
  assert/1 unit = >.

  def zap/1 = unit (()) twee z i z.
  assert/1 zap = -.

  def swap/2 = unit (unit) twee (()) twee z i z i i unit twee (()) twee z i z i i.
  assert/2 swap = ~.

  def dup/1 = () twee i swap i.
  assert/1 dup = +.

  def cat/2 = swap twee (()) twee z i z i.
  assert/2 cat = ,.
end twee_z

namespace cwud_z
  def i/1  = () z.
  assert/1 i = <.

  def swap/2 = () cwud z.
  assert/2 swap = ~.

  def dup/1 = () () cwud cwud z z.
  assert/1 dup = +.

  def zap/1 = () swap z.
  assert/1 zap = -.

  def unit/1 = () () cwud zap swap zap.
  assert/1 unit = >.

  def cat/2 = (() swap) swap unit cwud z swap i cwud z zap.
  assert/2 cat = ,.
end cwud_z

namespace cake_k
  def zap/1 = () k.
  assert/1 zap = -.

  def unit/1 = () cake zap.
  assert/1 unit = >.

  def swap/2 = unit cake k.
  assert/2 swap = ~.

  def i/1  = () swap k.
  assert/1 i = <.

  def dup/1 = () cake i swap i.
  assert/1 dup = +.

  def cat/2 = ((unit) cake k i) cake()k cake()k.
    assert/2 cat = ,.
end cake_k
