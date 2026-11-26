-- Prove2me | Theorems.Thm_JacobianCounterexample_not_jacobian_conjecture_complex
-- name    : JacobianCounterexample.not_jacobian_conjecture_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:05.202541+00:00
-- url     : https://prove2.me/theorems/d46f2daf-2388-4448-871f-0c162e32544f
-- title:
--   Jacobian Counterexample: not jacobian conjecture complex
-- statement:
--   The usual dimension-three Jacobian-conjecture statement is false over `ℂ`.
--
--   The witness is `F`: its formal Jacobian determinant is a nonzero constant,
--   while two distinct rational points have the same image.
--
--   Source: https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L74-L89
-- source:
--   https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L74-L89

import Definitions.Def_JacobianConjecture_Definitions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_JacobianConjecture_Proof
set_option autoImplicit true
noncomputable section
open Matrix Function
open MvPolynomial
open JacobianCounterexample
variable (K : Type*) [Field K]
variable {K}

theorem JacobianCounterexample.not_jacobian_conjecture_complex :
    ¬ ∀ P : Fin 3 → MvPolynomial (Fin 3) ℂ,
      IsUnit (MvPolynomial.jacobianDet P) →
        Injective (MvPolynomial.evalMap P) := by sorry
