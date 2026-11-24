-- Prove2me | Theorems.Thm_GlobalTheory_LimitOfDivisibility_exists_limit_of_pow_dvd_sub
-- name    : GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:04:34.523974+00:00
-- url     : https://prove2.me/theorems/58165ae0-2549-4473-9183-622814295ba9
-- title:
--   Limit Of Divisibility: exists limit of pow dvd sub
-- statement:
--   The Limit Of Divisibility construction uses the exists limit of pow dvd sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLimitOfPowDvdSub.lean#L5-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLimitOfPowDvdSub.lean#L5-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLimitOfPowDvdSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LimitOfDivisibility

theorem GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub {R : Type} [inst : CommRing R] (p : ℕ)
    [IsAdicComplete (Ideal.span {(↑p : R)}) R] (f : ℕ → R)
    (h : ∀ (n : ℕ), (↑p : R) ^ n ∣ f (n + (1 : ℕ)) - f n) :
    ∃ (L : R), ∀ (n : ℕ), (↑p : R) ^ n ∣ L - f n := by sorry
