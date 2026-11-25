-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_support_eq_union_of_shortExact
-- name    : GlobalTheory.QCoh.support_eq_union_of_shortExact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:06:23.729495+00:00
-- url     : https://prove2.me/theorems/44398b97-541d-4c31-9164-2618011c00e0
-- title:
--   QCoh: support eq union of short Exact
-- statement:
--   The QCoh construction uses the support eq union of short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L519-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L519-L524

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

theorem GlobalTheory.QCoh.support_eq_union_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    support S.X₂ = support S.X₁ ∪ support S.X₃ := by sorry
