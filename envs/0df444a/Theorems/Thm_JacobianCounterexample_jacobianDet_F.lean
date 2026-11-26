-- Prove2me | Theorems.Thm_JacobianCounterexample_jacobianDet_F
-- name    : JacobianCounterexample.jacobianDet_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:01.945203+00:00
-- url     : https://prove2.me/theorems/4466c9b8-9593-48fd-993c-e4dcc81f75e3
-- title:
--   Jacobian Counterexample: jacobian Det F
-- statement:
--   The formal Jacobian determinant of `F` is the constant polynomial `-2`.
--
--   Source: https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L27-L35
-- source:
--   https://github.com/Arthur742Ramos/jacobian-conjecture-lean/blob/8db55ea3ffa8ba90094d6ef78ee3351ddfce01ca/JacobianConjecture/Proof.lean#L27-L35

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

theorem JacobianCounterexample.jacobianDet_F : MvPolynomial.jacobianDet (F K) = C (-2) := by sorry
