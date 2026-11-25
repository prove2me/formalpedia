-- Prove2me | Theorems.Thm_GlobalTheory_two_mul_pow_four_dvd_card_generalLinearGroup
-- name    : GlobalTheory.two_mul_pow_four_dvd_card_generalLinearGroup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:09.148393+00:00
-- url     : https://prove2.me/theorems/d77f6caf-61f9-46b4-a761-ee4db766943b
-- title:
--   Global Theory: two mul pow four dvd card general Linear Group
-- statement:
--   The Global Theory construction uses the two mul pow four dvd card general Linear Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TwoMulPowFourDvdCardGeneralLinearGroup.lean#L38-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TwoMulPowFourDvdCardGeneralLinearGroup.lean#L38-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.two_mul_pow_four_dvd_card_generalLinearGroup :
    ∀ (R : Type) [CommRing R] [Finite R] (p : ℕ), Odd p → CharP R (p ^ 4) → 1 < p →
      ∀ r : ℕ, 2 ≤ r → 2 * p ^ 4 ∣ Nat.card (GL (Fin r) R) := by sorry
