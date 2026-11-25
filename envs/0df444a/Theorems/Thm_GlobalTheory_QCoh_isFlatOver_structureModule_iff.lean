-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isFlatOver_structureModule_iff
-- name    : GlobalTheory.QCoh.isFlatOver_structureModule_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:44.384444+00:00
-- url     : https://prove2.me/theorems/c81eedee-291f-4d8f-a01d-7248a4a16e3f
-- title:
--   QCoh: is Flat Over structure Module iff
-- statement:
--   The QCoh construction uses the is Flat Over structure Module iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1362-L1364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1362-L1364

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

theorem GlobalTheory.QCoh.isFlatOver_structureModule_iff :
    IsFlatOver (structureModule X) ρ ↔ ∀ U : X.Opens, IsAffineOpen U → (baseHom U ρ).Flat := by sorry
