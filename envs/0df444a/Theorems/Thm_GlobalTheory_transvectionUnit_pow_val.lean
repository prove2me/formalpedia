-- Prove2me | Theorems.Thm_GlobalTheory_transvectionUnit_pow_val
-- name    : GlobalTheory.transvectionUnit_pow_val
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:23:34.356688+00:00
-- url     : https://prove2.me/theorems/be423549-b979-4d39-83b1-85acf81eef99
-- title:
--   Global Theory: transvection Unit pow val
-- statement:
--   The Global Theory construction uses the transvection Unit pow val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TwoMulPowFourDvdCardGeneralLinearGroup.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TwoMulPowFourDvdCardGeneralLinearGroup.lean#L12-L22

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

theorem GlobalTheory.transvectionUnit_pow_val {R : Type} [CommRing R] {r : ℕ} {i j : Fin r} (h : i ≠ j)
    (n : ℕ) :
    ((transvectionUnit (R := R) h ^ n : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)
      = transvection i j (n : R) := by sorry
