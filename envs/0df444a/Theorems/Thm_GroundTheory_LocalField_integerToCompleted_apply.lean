-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integerToCompleted_apply
-- name    : GroundTheory.LocalField.integerToCompleted_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:52.958854+00:00
-- url     : https://prove2.me/theorems/d95d7c1f-3d36-4848-b428-587e561d0b5e
-- title:
--   Local Field: integer To Completed apply
-- statement:
--   The Local Field construction uses the integer To Completed apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L557-L559
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L557-L559

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open IsLocalRing ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
local notation "𝔹" => CompletedUnramifiedIntegers K Ω
variable {K Ω}

theorem GroundTheory.LocalField.integerToCompleted_apply {L : IntermediateField K Ω} (h : L ≤ 𝔼) (x : 𝒪[L]) :
    integerToCompleted K Ω h x = algebraMap 𝒪[𝔼] 𝔹 (integerInclusion h x) := by sorry

attribute [defeq] GroundTheory.LocalField.integerToCompleted_apply
