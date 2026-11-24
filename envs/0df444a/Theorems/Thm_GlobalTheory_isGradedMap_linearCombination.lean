-- Prove2me | Theorems.Thm_GlobalTheory_isGradedMap_linearCombination
-- name    : GlobalTheory.isGradedMap_linearCombination
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:24.973033+00:00
-- url     : https://prove2.me/theorems/20c2ec8c-97db-43be-9ab5-454934386fa8
-- title:
--   Global Theory: is Graded Map linear Combination
-- statement:
--   The Global Theory construction uses the is Graded Map linear Combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L492-L498
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L492-L498

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R] {κ : Type*}
  {M : κ → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]

theorem GlobalTheory.isGradedMap_linearCombination [Fintype κ] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩]
    {g : κ → N} {d : κ → ℤ} (hg : ∀ k, g k ∈ 𝒩 (d k)) :
    IsGradedMap (grFree ι R d) 𝒩 (Fintype.linearCombination (MvPolynomial ι R) g) := by sorry
