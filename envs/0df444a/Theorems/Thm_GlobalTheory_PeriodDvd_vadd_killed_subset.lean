-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDvd_vadd_killed_subset
-- name    : GlobalTheory.PeriodDvd.vadd_killed_subset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:17.302669+00:00
-- url     : https://prove2.me/theorems/437c34f8-0a45-4d9e-8df5-860207aa4973
-- title:
--   Period Dvd: vadd killed subset
-- statement:
--   The Period Dvd construction uses the vadd killed subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L105-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L105-L112

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

theorem GlobalTheory.PeriodDvd.vadd_killed_subset {d : ℕ} [NeZero d] (I : Finset (ZMod d)) {x : ZMod d} (hx : x ∈ I) :
    x +ᵥ killed d (Nat.card (AddAction.stabilizer (ZMod d) I)) ⊆ I := by sorry
