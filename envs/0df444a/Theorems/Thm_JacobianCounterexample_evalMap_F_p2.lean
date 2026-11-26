-- Prove2me | Theorems.Thm_JacobianCounterexample_evalMap_F_p2
-- name    : JacobianCounterexample.evalMap_F_p2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:58:59.89629+00:00
-- url     : https://prove2.me/theorems/c5a64066-68bc-510f-a275-2082b31619e8
-- title:
--   Jacobian Counterexample: eval Map F p2
-- statement:
--   The third point in the published three-point fibre.
--
--   Source: https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L54-L59
-- source:
--   https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L54-L59

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

theorem JacobianCounterexample.evalMap_F_p2 (h2 : (2 : K) ≠ 0) :
    MvPolynomial.evalMap (F K) ![-1, 3 / 2, 13 / 2] = ![-(1 / 4), 0, 0] := by sorry
