-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDvd_val_mul
-- name    : GlobalTheory.PeriodDvd.val_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:14.113618+00:00
-- url     : https://prove2.me/theorems/1d1f58fb-3259-473e-b086-f49d9d04442b
-- title:
--   Period Dvd: val mul
-- statement:
--   The Period Dvd construction uses the val mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L41-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd

theorem GlobalTheory.PeriodDvd.val_mul {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) {j : ℕ} (hj : j < s) :
    ((e * j : ℕ) : ZMod d).val = e * j := by sorry
