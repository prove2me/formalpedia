-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDvd_injOn_mul
-- name    : GlobalTheory.PeriodDvd.injOn_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:36.681927+00:00
-- url     : https://prove2.me/theorems/a9de75a4-d8b7-4b74-bce3-4d754e1396ef
-- title:
--   Period Dvd: inj On mul
-- statement:
--   The Period Dvd construction uses the inj On mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L49-L59

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

theorem GlobalTheory.PeriodDvd.injOn_mul {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) :
    Set.InjOn (fun j => ((e * j : ℕ) : ZMod d)) (Finset.range s : Set ℕ) := by sorry
