-- Prove2me | Theorems.Thm_GlobalTheory_span_localization_saturation
-- name    : GlobalTheory.span_localization_saturation
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:31.658285+00:00
-- url     : https://prove2.me/theorems/aa76a91d-8316-4994-ad27-648e33ff6d55
-- title:
--   Global Theory: span localization saturation
-- statement:
--   The Global Theory construction uses the span localization saturation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L733-L758
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L733-L758

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R)
  [IsLocalization p S] {V : Type*} [AddCommGroup V] [Module R V] [Module S V]
  [IsScalarTower R S V]
include p

theorem GlobalTheory.span_localization_saturation (hp : p ≤ R⁰) (N : Submodule R V) :
    Submodule.span S (saturation N : Set V) = saturation (Submodule.span S (N : Set V)) := by sorry
