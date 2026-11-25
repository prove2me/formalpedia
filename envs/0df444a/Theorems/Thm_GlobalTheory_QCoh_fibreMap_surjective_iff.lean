-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_fibreMap_surjective_iff
-- name    : GlobalTheory.QCoh.fibreMap_surjective_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:02:35.209804+00:00
-- url     : https://prove2.me/theorems/56819653-36f4-51f9-a1f0-b126fbacb60b
-- title:
--   QCoh: fibre Map surjective iff
-- statement:
--   The QCoh construction uses the fibre Map surjective iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1141-L1148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1141-L1148

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

theorem GlobalTheory.QCoh.fibreMap_surjective_iff (φ : F ⟶ G) [IsFiniteQC G] (x : X) :
    Function.Surjective (fibreMap φ x) ↔ Function.Surjective (stalkLinear φ x) := by sorry
