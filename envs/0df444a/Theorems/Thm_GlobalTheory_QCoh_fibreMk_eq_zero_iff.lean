-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_fibreMk_eq_zero_iff
-- name    : GlobalTheory.QCoh.fibreMk_eq_zero_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:22.941113+00:00
-- url     : https://prove2.me/theorems/6fdd5a40-4ac0-4eb7-b609-87d3c870853e
-- title:
--   QCoh: fibre Mk eq zero iff
-- statement:
--   The QCoh construction uses the fibre Mk eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1050-L1054
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1050-L1054

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

theorem GlobalTheory.QCoh.fibreMk_eq_zero_iff (x : X) (t : (F.presheaf.stalk x :)) :
    fibreMk F x t = 0 ↔ t ∈ (maximalIdeal (X.presheaf.stalk x) • ⊤ :
      Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) := by sorry
