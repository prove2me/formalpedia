-- Prove2me | Theorems.Thm_GlobalTheory_orderOf_transvectionUnit
-- name    : GlobalTheory.orderOf_transvectionUnit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:58.669268+00:00
-- url     : https://prove2.me/theorems/4892a5b2-4c18-49f5-bc6b-ed9f765e13c4
-- title:
--   Global Theory: order Of transvection Unit
-- statement:
--   The Global Theory construction uses the order Of transvection Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TwoMulPowFourDvdCardGeneralLinearGroup.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TwoMulPowFourDvdCardGeneralLinearGroup.lean#L24-L36

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

theorem GlobalTheory.orderOf_transvectionUnit {R : Type} [CommRing R] (q : ℕ) [CharP R q] {r : ℕ}
    {i j : Fin r} (h : i ≠ j) : orderOf (transvectionUnit (R := R) h) = q := by sorry
