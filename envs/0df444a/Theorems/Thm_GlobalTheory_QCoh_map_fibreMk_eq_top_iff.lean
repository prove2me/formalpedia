-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_map_fibreMk_eq_top_iff
-- name    : GlobalTheory.QCoh.map_fibreMk_eq_top_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:04:09.848626+00:00
-- url     : https://prove2.me/theorems/53c3d53c-04e3-49e0-bae9-05735cf43601
-- title:
--   QCoh: map fibre Mk eq top iff
-- statement:
--   The QCoh construction uses the map fibre Mk eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1129-L1132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1129-L1132

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

theorem GlobalTheory.QCoh.map_fibreMk_eq_top_iff [IsFiniteQC F] (x : X)
    (N : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) :
    N.map (fibreMk F x) = ⊤ ↔ N = ⊤ := by sorry
