-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_IsFlatOver_restrict
-- name    : GlobalTheory.QCoh.IsFlatOver.restrict
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:59.863128+00:00
-- url     : https://prove2.me/theorems/2fdd0828-c0ce-4db1-b8e1-0eb48a457c2d
-- title:
--   Is Flat Over: restrict
-- statement:
--   The Is Flat Over construction uses the restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1338-L1357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1338-L1357

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

theorem GlobalTheory.QCoh.IsFlatOver.restrict (h : IsFlatOver F ρ) {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] : IsFlatOver (F.restrict g) (g.appTop.hom.comp ρ) := by sorry
