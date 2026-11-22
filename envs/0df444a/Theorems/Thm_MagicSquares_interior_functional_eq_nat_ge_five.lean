-- Prove2me | Theorems.Thm_MagicSquares_interior_functional_eq_nat_ge_five
-- name    : MagicSquares.interior_functional_eq_nat_ge_five
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-21T22:18:28.411762+00:00
-- url     : https://prove2.me/theorems/561721cd-6a18-422a-83f3-9ef47de790ff
-- title:
--   Functional equation for n at least five
-- statement:
--   Let n >= 5 and p in Q[X] agree with H_n on all naturals. Then for every natural u,p(-n-u) = (-1)^{(n-1)^2} p(u).This is the remaining hard core after the n equal one through four cases, which are proved via explicit polynomials. Combined with those cases by splitting on n, it yields the general natural-shift functional equation.**Formalization Note** Lean writes rationals as Rat; hypothesis is 5 <= n, stronger than 1 <= n.
-- source:
--   R. P. Stanley, Duke Math. J. 40 (1973), 607--632; E. Ehrhart (1973); M. Beck et al., Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013), remaining core n at least five.

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem interior_functional_eq_nat_ge_five (n : Nat) (hn : 5 <= n) (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount n t : Rat)) (u : Nat) :
    p.eval (-(((n + u : Nat)) : Rat)) = (-1 : Rat) ^ ((n - 1) ^ 2) * p.eval ((u : Rat)) := by sorry

end MagicSquares
