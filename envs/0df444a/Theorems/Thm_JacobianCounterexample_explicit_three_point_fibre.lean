-- Prove2me | Theorems.Thm_JacobianCounterexample_explicit_three_point_fibre
-- name    : JacobianCounterexample.explicit_three_point_fibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:02.472594+00:00
-- url     : https://prove2.me/theorems/38696fdd-e0fc-4cc6-80cf-c838e19b5acd
-- title:
--   Jacobian Counterexample: explicit three point fibre
-- statement:
--   The three displayed rational points lie in one fibre over `ℂ`.
--
--   Source: https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L62-L68
-- source:
--   https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L62-L68

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

theorem JacobianCounterexample.explicit_three_point_fibre :
    MvPolynomial.evalMap (F ℂ) ![0, 0, -(1 / 4)] = ![-(1 / 4), 0, 0] ∧
      MvPolynomial.evalMap (F ℂ) ![1, -(3 / 2), 13 / 2] = ![-(1 / 4), 0, 0] ∧
      MvPolynomial.evalMap (F ℂ) ![-1, 3 / 2, 13 / 2] = ![-(1 / 4), 0, 0] := by sorry
