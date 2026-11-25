-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_mem_assPoints_iff_exists_pow
-- name    : GlobalTheory.QCoh.mem_assPoints_iff_exists_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:10.775818+00:00
-- url     : https://prove2.me/theorems/a2edeeb2-4dda-44e2-8357-fef0fa1bf726
-- title:
--   QCoh: mem ass Points iff exists pow
-- statement:
--   The QCoh construction uses the mem ass Points iff exists pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L773-L780
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L773-L780

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

theorem GlobalTheory.QCoh.mem_assPoints_iff_exists_pow {x : X} :
    x ∈ assPoints F ↔ ∃ t : (F.presheaf.stalk x :),
      ∀ r : X.presheaf.stalk x, (∃ n : ℕ, r ^ n • t = 0) ↔ ¬ IsUnit r := by sorry
