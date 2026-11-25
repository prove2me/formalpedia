-- Prove2me | Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionFrobenius_inclusion
-- name    : GroundTheory.LocalField.maximalUnramifiedExtensionFrobenius_inclusion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:09:44.732158+00:00
-- url     : https://prove2.me/theorems/3f907e59-a386-5e5a-8eca-af96dca986f1
-- title:
--   Local Field: maximal Unramified Extension Frobenius inclusion
-- statement:
--   The Local Field construction uses the maximal Unramified Extension Frobenius inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L588-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L588-L615

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_ramificationIndex_eq_one

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
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
local notation "𝔹" => CompletedUnramifiedIntegers K Ω

theorem GroundTheory.LocalField.maximalUnramifiedExtensionFrobenius_inclusion {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) (y : L) :
    letI := hL.1
    ((maximalUnramifiedExtensionFrobenius K Ω
      (IntermediateField.inclusion hL.le_maximalUnramifiedExtension y) : 𝔼) : Ω) =
      ((frobenius K L hL.ramificationIndex_eq_one y : L) : Ω) := by sorry
