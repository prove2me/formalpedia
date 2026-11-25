-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_completedUnramifiedAlgEquiv
-- name    : GroundTheory.LocalField.eq_completedUnramifiedAlgEquiv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:26.137925+00:00
-- url     : https://prove2.me/theorems/925e06e1-0de1-5509-a2b8-02a93a6201ed
-- title:
--   Local Field: eq completed Unramified Alg Equiv
-- statement:
--   The Local Field construction uses the eq completed Unramified Alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L478-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L478-L482

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

theorem GroundTheory.LocalField.eq_completedUnramifiedAlgEquiv (ρ : 𝔼 ≃ₐ[K] 𝔼) {τ : 𝔹 →+* 𝔹}
    (hτ : ∀ x : 𝒪[𝔼], τ (algebraMap 𝒪[𝔼] 𝔹 x) =
      algebraMap 𝒪[𝔼] 𝔹 (integerAlgEquivOfIsAlgebraic K 𝔼 ρ x)) :
    τ = (completedUnramifiedAlgEquiv K Ω ρ : 𝔹 →+* 𝔹) := by sorry
