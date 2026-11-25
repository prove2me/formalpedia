-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_IsFlatOver_of_sum_eq_id
-- name    : GlobalTheory.QCoh.IsFlatOver.of_sum_eq_id
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:03:54.899733+00:00
-- url     : https://prove2.me/theorems/01de70f8-319a-4123-8345-e66ad7c78780
-- title:
--   Is Flat Over: of sum eq id
-- statement:
--   The Is Flat Over construction uses the of sum eq id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1302-L1315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1302-L1315

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))
variable {ρ}

theorem GlobalTheory.QCoh.IsFlatOver.of_sum_eq_id {ι : Type*} [Fintype ι] {A : ι → X.Modules} (p : ∀ i, F ⟶ A i)
    (q : ∀ i, A i ⟶ F) (h : ∑ i, p i ≫ q i = 𝟙 F) (hA : ∀ i, IsFlatOver (A i) ρ) :
    IsFlatOver F ρ := by sorry
