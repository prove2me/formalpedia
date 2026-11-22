-- Prove2me | Theorems.Thm_MagicSquares_interior_functional_eq_nat_one
-- name    : MagicSquares.interior_functional_eq_nat_one
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-21T22:18:18.078914+00:00
-- url     : https://prove2.me/theorems/4e0a58cc-b956-402f-9382-07df8670d02d
-- title:
--   Functional equation for n equal one
-- statement:
--   Let p in Q[X] agree with H_1 on all naturals. Then for every natural u,p(-1-u) = (-1)^{0} p(u).Since (1-1)^2 is zero the sign is one. H_1 is constantly one, so p is constantly one and both sides equal one. This is the n equal one case of the natural-shift functional equation, used with the two, three, four and n at least five cases to imply the general statement by splitting on n.**Formalization Note** Lean writes rationals as Rat with explicit casts; n is fixed to one so no order hypothesis is needed.
-- source:
--   R. P. Stanley, Duke Math. J. 40 (1973), 607--632; M. Beck et al., Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013), specialized to n equal one.

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem interior_functional_eq_nat_one (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount 1 t : Rat)) (u : Nat) :
    p.eval (-(((1 + u : Nat)) : Rat)) = (-1 : Rat) ^ ((1 - 1) ^ 2) * p.eval ((u : Rat)) := by sorry

end MagicSquares
