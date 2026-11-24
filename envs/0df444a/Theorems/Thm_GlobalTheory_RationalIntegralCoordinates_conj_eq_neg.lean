-- Prove2me | Theorems.Thm_GlobalTheory_RationalIntegralCoordinates_conj_eq_neg
-- name    : GlobalTheory.RationalIntegralCoordinates.conj_eq_neg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:13:13.495481+00:00
-- url     : https://prove2.me/theorems/7e4fa5da-9a99-4ce9-b163-f1d9e17c8092
-- title:
--   Rational Integral Coordinates: conj eq neg
-- statement:
--   The Rational Integral Coordinates construction uses the conj eq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IntOfPrimeMulSq.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IntOfPrimeMulSq.lean#L29-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RationalIntegralCoordinates

theorem GlobalTheory.RationalIntegralCoordinates.conj_eq_neg {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) r = -r := by sorry
