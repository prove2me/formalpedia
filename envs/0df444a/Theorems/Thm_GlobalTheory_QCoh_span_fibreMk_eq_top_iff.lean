-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_span_fibreMk_eq_top_iff
-- name    : GlobalTheory.QCoh.span_fibreMk_eq_top_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:53.987301+00:00
-- url     : https://prove2.me/theorems/7cc038aa-974f-5401-b773-a86e6f3296c4
-- title:
--   QCoh: span fibre Mk eq top iff
-- statement:
--   The QCoh construction uses the span fibre Mk eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1134-L1139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1134-L1139

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

theorem GlobalTheory.QCoh.span_fibreMk_eq_top_iff [IsFiniteQC F] (x : X) (s : Set (F.presheaf.stalk x :)) :
    Submodule.span (X.residueField x) (fibreMk F x '' s) = ⊤ ↔
      Submodule.span (X.presheaf.stalk x) s = ⊤ := by sorry
