-- Prove2me | Theorems.Thm_GlobalTheory_isReduced_of_smooth_over_field
-- name    : GlobalTheory.isReduced_of_smooth_over_field
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:07.336792+00:00
-- url     : https://prove2.me/theorems/dc0f3a98-b6e9-488b-99bd-0759acdc48ee
-- title:
--   Global Theory: is Reduced of smooth over field
-- statement:
--   The Global Theory construction uses the is Reduced of smooth over field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsReducedOfSmoothOverField.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsReducedOfSmoothOverField.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedOfSmoothOverField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.isReduced_of_smooth_over_field (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] : IsReduced A := by sorry
