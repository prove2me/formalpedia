-- Prove2me | Theorems.Thm_GlobalTheory_span_localization_saturationIn
-- name    : GlobalTheory.span_localization_saturationIn
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:30.188675+00:00
-- url     : https://prove2.me/theorems/4f4c186f-08b7-428f-93dc-1b4c8a8e0ea4
-- title:
--   Global Theory: span localization saturation In
-- statement:
--   The Global Theory construction uses the span localization saturation In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L760-L764
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L760-L764

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

theorem GlobalTheory.span_localization_saturationIn (hp : p ≤ R⁰) (M N : Submodule R V) :
    Submodule.span S (saturationIn M N : Set V) =
      saturationIn (Submodule.span S (M : Set V)) (Submodule.span S (N : Set V)) := by sorry
