-- Prove2me | Theorems.Thm_GlobalTheory_IterGain_mem_letters
-- name    : GlobalTheory.IterGain.mem_letters
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:22:47.409704+00:00
-- url     : https://prove2.me/theorems/630e0b01-097c-49ca-8580-c04095354c20
-- title:
--   Iter Gain: mem letters
-- statement:
--   The Iter Gain construction uses the mem letters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecay.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecay.lean#L19-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.IterGain

theorem GlobalTheory.IterGain.mem_letters {ι : Type} [DecidableEq ι] (B : Finset ι) :
    ∀ (k : ℕ), ∀ l ∈ words B k, ∀ i ∈ l, i ∈ B := by sorry
