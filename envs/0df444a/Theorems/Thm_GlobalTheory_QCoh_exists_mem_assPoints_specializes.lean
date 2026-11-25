-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_exists_mem_assPoints_specializes
-- name    : GlobalTheory.QCoh.exists_mem_assPoints_specializes
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:05:52.46457+00:00
-- url     : https://prove2.me/theorems/9f8dc57a-54a2-4452-85dc-34df605e8490
-- title:
--   QCoh: exists mem ass Points specializes
-- statement:
--   The QCoh construction uses the exists mem ass Points specializes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L876-L893
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L876-L893

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
variable [IsLocallyNoetherian X]

theorem GlobalTheory.QCoh.exists_mem_assPoints_specializes [F.IsQuasicoherent] {x : X} (hx : x ∈ support F) :
    ∃ y ∈ assPoints F, y ⤳ x := by sorry
