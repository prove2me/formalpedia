-- Prove2me | Theorems.Thm_JacobianCounterexample_evalMap_F_p0
-- name    : JacobianCounterexample.evalMap_F_p0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:02.135672+00:00
-- url     : https://prove2.me/theorems/03b4a053-0755-44c9-9c10-6421cf2d5c1b
-- title:
--   Jacobian Counterexample: eval Map F p0
-- statement:
--   The first point in the published three-point fibre.
--
--   Source: https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L40-L43
-- source:
--   https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L40-L43

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

theorem JacobianCounterexample.evalMap_F_p0 :
    MvPolynomial.evalMap (F K) ![0, 0, -(1 / 4)] = ![-(1 / 4), 0, 0] := by sorry
