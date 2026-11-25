-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isIrreducible_of_image
-- name    : GlobalTheory.QCoh.isIrreducible_of_image
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:03:36.060644+00:00
-- url     : https://prove2.me/theorems/624028da-e082-5a84-8cd5-5e52fb644aac
-- title:
--   QCoh: is Irreducible of image
-- statement:
--   The QCoh construction uses the is Irreducible of image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L639-L645
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L639-L645

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

theorem GlobalTheory.QCoh.isIrreducible_of_image {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] {f : S → T}
    (hf : Topology.IsInducing f) {s : Set S} (h : IsIrreducible (f '' s)) : IsIrreducible s := by sorry
