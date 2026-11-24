-- Prove2me | Theorems.Thm_GlobalTheory_mixedSpace_norm_ne_zero_iff_isUnit
-- name    : GlobalTheory.mixedSpace_norm_ne_zero_iff_isUnit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:00.317688+00:00
-- url     : https://prove2.me/theorems/c3f18b4a-ef29-49c3-b6b4-31cf0e707146
-- title:
--   Global Theory: mixed Space norm ne zero iff is Unit
-- statement:
--   The Global Theory construction uses the mixed Space norm ne zero iff is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSmoothMulExtensionOfContinuousChar.lean#L91-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSmoothMulExtensionOfContinuousChar.lean#L91-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.mixedSpace_norm_ne_zero_iff_isUnit (K : Type) [Field K] [NumberField K]
    (x : mixedSpace K) : mixedEmbedding.norm x ≠ 0 ↔ IsUnit x := by sorry
