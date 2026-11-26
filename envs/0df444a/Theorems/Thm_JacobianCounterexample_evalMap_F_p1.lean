-- Prove2me | Theorems.Thm_JacobianCounterexample_evalMap_F_p1
-- name    : JacobianCounterexample.evalMap_F_p1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:58:58.035694+00:00
-- url     : https://prove2.me/theorems/50a3088a-8af4-5f7c-a5b8-f40b3fed25a1
-- title:
--   Jacobian Counterexample: eval Map F p1
-- statement:
--   The second point in the published three-point fibre.
--
--   Source: https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L46-L51
-- source:
--   https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L46-L51

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

theorem JacobianCounterexample.evalMap_F_p1 (h2 : (2 : K) ≠ 0) :
    MvPolynomial.evalMap (F K) ![1, -(3 / 2), 13 / 2] = ![-(1 / 4), 0, 0] := by sorry
