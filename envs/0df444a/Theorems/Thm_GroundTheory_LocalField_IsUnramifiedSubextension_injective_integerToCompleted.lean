-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_injective_integerToCompleted
-- name    : GroundTheory.LocalField.IsUnramifiedSubextension.injective_integerToCompleted
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:52.726205+00:00
-- url     : https://prove2.me/theorems/e571bb8f-35f5-4b1a-b632-f96c7320a6a8
-- title:
--   Is Unramified Subextension: injective integer To Completed
-- statement:
--   The Is Unramified Subextension construction uses the injective integer To Completed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L570-L573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L570-L573

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

theorem GroundTheory.LocalField.IsUnramifiedSubextension.injective_integerToCompleted {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) :
    Function.Injective (integerToCompleted K Ω hL.le_maximalUnramifiedExtension) := by sorry
