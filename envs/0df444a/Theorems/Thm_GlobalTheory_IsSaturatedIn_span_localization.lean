-- Prove2me | Theorems.Thm_GlobalTheory_IsSaturatedIn_span_localization
-- name    : GlobalTheory.IsSaturatedIn.span_localization
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:56.291253+00:00
-- url     : https://prove2.me/theorems/6680721f-7510-5045-ac05-272ee919e96f
-- title:
--   Is Saturated In: span localization
-- statement:
--   The Is Saturated In construction uses the span localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L766-L770
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L766-L770

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

theorem GlobalTheory.IsSaturatedIn.span_localization (hp : p ≤ R⁰) {M N : Submodule R V}
    (h : IsSaturatedIn M N) :
    IsSaturatedIn (Submodule.span S (M : Set V)) (Submodule.span S (N : Set V)) := by sorry
