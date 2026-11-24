-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_det_diagGL
-- name    : GlobalTheory.SplitFlip.det_diagGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:55.259702+00:00
-- url     : https://prove2.me/theorems/c23003d6-c6be-4336-884c-c523149874b0
-- title:
--   Split Flip: det diag GL
-- statement:
--   The Split Flip construction uses the det diag GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/T2SpaceGeneralLinearGroup.lean#L93-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/T2SpaceGeneralLinearGroup.lean#L93-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SplitFlip.det_diagGL (c : n → kˣ) : Matrix.GeneralLinearGroup.det (diagGL c) = ∏ i, c i := by sorry
