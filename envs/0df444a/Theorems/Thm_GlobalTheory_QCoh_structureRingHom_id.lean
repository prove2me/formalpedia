-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_structureRingHom_id
-- name    : GlobalTheory.QCoh.structureRingHom_id
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:12:25.811561+00:00
-- url     : https://prove2.me/theorems/4efa948f-6b88-51eb-8424-4447275a0ab4
-- title:
--   QCoh: structure Ring Hom id
-- statement:
--   The QCoh construction uses the structure Ring Hom id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1389-L1391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1389-L1391

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

theorem GlobalTheory.QCoh.structureRingHom_id {R : CommRingCat.{u}} :
    structureRingHom (𝟙 (Spec R)) = (Scheme.ΓSpecIso R).inv.hom := by sorry
