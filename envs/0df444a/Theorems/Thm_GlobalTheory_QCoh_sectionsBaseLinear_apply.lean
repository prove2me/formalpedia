-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_sectionsBaseLinear_apply
-- name    : GlobalTheory.QCoh.sectionsBaseLinear_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:28:35.062491+00:00
-- url     : https://prove2.me/theorems/88867a5c-bedb-40f6-8232-4a7e8d64e110
-- title:
--   QCoh: sections Base Linear apply
-- statement:
--   The QCoh construction uses the sections Base Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1299-L1300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1299-L1300

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

theorem GlobalTheory.QCoh.sectionsBaseLinear_apply (φ : F ⟶ G) (s : Γ(F, U)) :
    sectionsBaseLinear ρ φ U s = φ.app U s := by sorry

attribute [defeq] GlobalTheory.QCoh.sectionsBaseLinear_apply
