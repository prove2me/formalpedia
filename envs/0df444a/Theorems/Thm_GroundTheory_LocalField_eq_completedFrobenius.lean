-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_completedFrobenius
-- name    : GroundTheory.LocalField.eq_completedFrobenius
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:24.057022+00:00
-- url     : https://prove2.me/theorems/724b9662-cffa-471c-af26-0c2e01a9ba4c
-- title:
--   Local Field: eq completed Frobenius
-- statement:
--   The Local Field construction uses the eq completed Frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L496-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L496-L500

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
variable [IsGalois K Ω]

theorem GroundTheory.LocalField.eq_completedFrobenius {τ : 𝔹 →+* 𝔹}
    (hτ : ∀ x : 𝒪[𝔼], τ (algebraMap 𝒪[𝔼] 𝔹 x) = algebraMap 𝒪[𝔼] 𝔹
      (integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x)) :
    τ = (completedFrobenius K Ω : 𝔹 →+* 𝔹) := by sorry
