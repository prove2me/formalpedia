-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_epi_iff_fibreMap_surjective
-- name    : GlobalTheory.QCoh.epi_iff_fibreMap_surjective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:46.659868+00:00
-- url     : https://prove2.me/theorems/2d891894-64dc-491e-9c87-25a377757213
-- title:
--   QCoh: epi iff fibre Map surjective
-- statement:
--   The QCoh construction uses the epi iff fibre Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1150-L1152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1150-L1152

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

theorem GlobalTheory.QCoh.epi_iff_fibreMap_surjective (φ : F ⟶ G) [IsFiniteQC G] :
    Epi φ ↔ ∀ x : X, Function.Surjective (fibreMap φ x) := by sorry
