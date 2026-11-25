-- Prove2me | Theorems.Thm_JacPoisson_poissonBracket_eq_mul
-- name    : JacPoisson.poissonBracket_eq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:50:48.529426+00:00
-- url     : https://prove2.me/theorems/8c68ab8d-83f5-4eac-ba01-d36b8c1cac70
-- title:
--   Jac Poisson: poisson Bracket eq mul
-- statement:
--   The bracket of two components of a polynomial map is an entry of `Jᵀ (-J₀) J`, where `J` is
--   the map's Jacobian and `J₀ = Matrix.J` the canonical skew-symmetric matrix.
--
--   Source: https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L39-L50
-- source:
--   https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L39-L50

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main
set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
variable {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]

theorem JacPoisson.poissonBracket_eq_mul (F : RegularFunction R (l ⊕ l) (l ⊕ l)) (v w : l ⊕ l) :
    poissonBracket (F v) (F w) =
      (F.Jacobianᵀ * (-Matrix.J l (MvPolynomial (l ⊕ l) R)) * F.Jacobian) v w := by sorry
