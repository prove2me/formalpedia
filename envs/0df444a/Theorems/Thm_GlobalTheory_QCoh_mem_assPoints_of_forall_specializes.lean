-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_mem_assPoints_of_forall_specializes
-- name    : GlobalTheory.QCoh.mem_assPoints_of_forall_specializes
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:55.649262+00:00
-- url     : https://prove2.me/theorems/5c581e15-2820-58ae-8163-f63bac50411f
-- title:
--   QCoh: mem ass Points of forall specializes
-- statement:
--   The QCoh construction uses the mem ass Points of forall specializes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L895-L898
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L895-L898

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

theorem GlobalTheory.QCoh.mem_assPoints_of_forall_specializes [F.IsQuasicoherent] {x : X} (hx : x ∈ support F)
    (h : ∀ y ∈ support F, y ⤳ x → y = x) : x ∈ assPoints F := by sorry
