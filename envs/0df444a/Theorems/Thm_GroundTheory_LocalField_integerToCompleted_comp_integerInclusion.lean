-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integerToCompleted_comp_integerInclusion
-- name    : GroundTheory.LocalField.integerToCompleted_comp_integerInclusion
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:22.273559+00:00
-- url     : https://prove2.me/theorems/4b56afc8-1843-5ee7-b5e7-76ae99d97028
-- title:
--   Local Field: integer To Completed comp integer Inclusion
-- statement:
--   The Local Field construction uses the integer To Completed comp integer Inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L565-L568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L565-L568

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

theorem GroundTheory.LocalField.integerToCompleted_comp_integerInclusion {L L' : IntermediateField K Ω} (h : L ≤ L')
    (h' : L' ≤ 𝔼) :
    (integerToCompleted K Ω h').comp (integerInclusion h) = integerToCompleted K Ω (h.trans h') := by sorry
