-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_ContractiveResolvent_cauchySeq_yosidaOperator_naturalShift_apply_operator
-- name    : MarkovProcess.Semigroup.ContractiveResolvent.cauchySeq_yosidaOperator_naturalShift_apply_operator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:36.178859+00:00
-- url     : https://prove2.me/theorems/bfc2352f-c849-4583-b277-512c42f34735
-- title:
--   MarkovProcess: cauchySeq_yosidaOperator_naturalShift_apply_operator
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaApproximation_2f7df37a
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaStrongLimit_932a76ce
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strong limits of Yosida approximations

This file constructs the canonical contraction obtained by taking the strong
limit of the Yosida exponentials along the shifts `n + 1`.  Continuity of its
orbits is proved in `Semigroup/Generation.lean`, from the criterion of
`Semigroup/OrbitContinuity.lean`.
-/

open Filter NormedSpace Set Topology

noncomputable section

namespace MarkovProcess.Semigroup







namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





section CompleteSpace

variable [CompleteSpace E]



















end CompleteSpace

end ContractiveResolvent

end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strong limits of Yosida approximations

This file constructs the canonical contraction obtained by taking the strong
limit of the Yosida exponentials along the shifts `n + 1`.  Continuity of its
orbits is proved in `Semigroup/Generation.lean`, from the criterion of
`Semigroup/OrbitContinuity.lean`.
-/

open Filter NormedSpace Set Topology










variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






variable [CompleteSpace E]

open MarkovProcess.Semigroup.ContractiveResolvent in

theorem MarkovProcess.Semigroup.ContractiveResolvent.cauchySeq_yosidaOperator_naturalShift_apply_operator
    (R : ContractiveResolvent E) (mu : PositiveShift) (t : NNReal) (y : E) :
    CauchySeq (fun n ↦ R.yosidaOperator (naturalShift n) t (R.operator mu y)) := by sorry
