-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDvd_mem_killed
-- name    : GlobalTheory.PeriodDvd.mem_killed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:49.482471+00:00
-- url     : https://prove2.me/theorems/a167bd6d-1201-42bd-a843-7f9178491f77
-- title:
--   Period Dvd: mem killed
-- statement:
--   The Period Dvd construction uses the mem killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L13-L14

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

theorem GlobalTheory.PeriodDvd.mem_killed {d : ℕ} [NeZero d] {s : ℕ} {x : ZMod d} : x ∈ killed d s ↔ s • x = 0 := by sorry
