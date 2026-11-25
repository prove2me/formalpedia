-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_topologicalKrullDim_le_of_isIrreducible
-- name    : GlobalTheory.QCoh.topologicalKrullDim_le_of_isIrreducible
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:45.407298+00:00
-- url     : https://prove2.me/theorems/c6a825ec-802e-5f4f-8cc1-1f7b3c81d884
-- title:
--   QCoh: topological Krull Dim le of is Irreducible
-- statement:
--   The QCoh construction uses the topological Krull Dim le of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L672-L679
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L672-L679

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

theorem GlobalTheory.QCoh.topologicalKrullDim_le_of_isIrreducible {T : Type*} [TopologicalSpace T] {s : Set T}
    {d : WithBot ℕ∞} (h : ∀ Z ⊆ s, IsIrreducible Z → topologicalKrullDim Z ≤ d) :
    topologicalKrullDim s ≤ d := by sorry
