-- Prove2me | Theorems.Thm_MagicSquares_interior_functional_eq_nat_four
-- name    : MagicSquares.interior_functional_eq_nat_four
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-21T22:18:24.365135+00:00
-- url     : https://prove2.me/theorems/c6af9734-1fb9-48ea-b1e9-8a1bcd20a1dc
-- title:
--   Functional equation for n equal four
-- statement:
--   Let p in Q[X] agree with H_4 on all naturals. Then for every natural u,p(-4-u) = (-1)^{9} p(u).Since (4-1)^2 is nine the sign is minus one. H_4 is Beck-Pixton polynomial of degree nine, so p equals that polynomial and both sides agree. This is the n equal four case.**Formalization Note** Lean writes rationals as Rat; n is fixed to four.
-- source:
--   M. Beck and D. Pixton, The Ehrhart polynomial of the Birkhoff polytope (arXiv:math/0202267); R. P. Stanley, Duke Math. J. 40 (1973), specialized to n equal four.

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem interior_functional_eq_nat_four (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount 4 t : Rat)) (u : Nat) :
    p.eval (-(((4 + u : Nat)) : Rat)) = (-1 : Rat) ^ ((4 - 1) ^ 2) * p.eval ((u : Rat)) := by sorry

end MagicSquares
