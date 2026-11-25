-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_topologicalKrullDim_le_of_irreducibleCloseds
-- name    : GlobalTheory.QCoh.topologicalKrullDim_le_of_irreducibleCloseds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:43.254155+00:00
-- url     : https://prove2.me/theorems/bc3318cf-0972-4128-9d03-7259c7b89081
-- title:
--   QCoh: topological Krull Dim le of irreducible Closeds
-- statement:
--   The QCoh construction uses the topological Krull Dim le of irreducible Closeds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L647-L666
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L647-L666

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

theorem GlobalTheory.QCoh.topologicalKrullDim_le_of_irreducibleCloseds {T : Type*} [TopologicalSpace T]
    {d : WithBot ℕ∞} (h : ∀ Z : IrreducibleCloseds T, topologicalKrullDim (Z : Set T) ≤ d) :
    topologicalKrullDim T ≤ d := by sorry
