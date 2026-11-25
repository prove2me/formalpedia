-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_support_subset_union_of_exact
-- name    : GlobalTheory.QCoh.support_subset_union_of_exact
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:12:11.194478+00:00
-- url     : https://prove2.me/theorems/598d0f66-3ca1-4c32-9b29-e0dbab062a8f
-- title:
--   QCoh: support subset union of exact
-- statement:
--   The QCoh construction uses the support subset union of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L509-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L509-L517

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

theorem GlobalTheory.QCoh.support_subset_union_of_exact {S : ShortComplex X.Modules} (hS : S.Exact) :
    support S.X₂ ⊆ support S.X₁ ∪ support S.X₃ := by sorry
