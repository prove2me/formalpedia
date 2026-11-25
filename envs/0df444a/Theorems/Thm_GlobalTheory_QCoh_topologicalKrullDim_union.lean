-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_topologicalKrullDim_union
-- name    : GlobalTheory.QCoh.topologicalKrullDim_union
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:03:10.076606+00:00
-- url     : https://prove2.me/theorems/be7a8cc3-a654-5c2d-bc36-8dd9f39353e3
-- title:
--   QCoh: topological Krull Dim union
-- statement:
--   The QCoh construction uses the topological Krull Dim union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L681-L689
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L681-L689

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

theorem GlobalTheory.QCoh.topologicalKrullDim_union {T : Type*} [TopologicalSpace T] {s t : Set T}
    (hs : IsClosed s) (ht : IsClosed t) :
    topologicalKrullDim (s ∪ t :) = max (topologicalKrullDim s) (topologicalKrullDim t) := by sorry
