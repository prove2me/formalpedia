-- Prove2me | Theorems.Thm_GlobalTheory_IterGain_append_mem
-- name    : GlobalTheory.IterGain.append_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:22:37.016883+00:00
-- url     : https://prove2.me/theorems/bd696b76-28ad-4162-88ca-2ca05a3efb23
-- title:
--   Iter Gain: append mem
-- statement:
--   The Iter Gain construction uses the append mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecay.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecay.lean#L14-L17

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

theorem GlobalTheory.IterGain.append_mem {ι : Type} [DecidableEq ι] {B : Finset ι} {k : ℕ} {l : List ι} {i : ι}
    (hl : l ∈ words B k) (hi : i ∈ B) : l ++ [i] ∈ words B (k + 1) := by sorry
