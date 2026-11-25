-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_mem_assPoints_iff_exists
-- name    : GlobalTheory.QCoh.mem_assPoints_iff_exists
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:04:38.53474+00:00
-- url     : https://prove2.me/theorems/d6a2eb22-af36-5c85-b8d1-add1f6e6fc75
-- title:
--   QCoh: mem ass Points iff exists
-- statement:
--   The QCoh construction uses the mem ass Points iff exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L793-L800
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L793-L800

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

theorem GlobalTheory.QCoh.mem_assPoints_iff_exists [IsLocallyNoetherian X] {x : X} :
    x ∈ assPoints F ↔ ∃ t : (F.presheaf.stalk x :),
      ∀ r : X.presheaf.stalk x, r • t = 0 ↔ r ∈ maximalIdeal (X.presheaf.stalk x) := by sorry
