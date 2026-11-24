-- Prove2me | Theorems.Thm_GlobalTheory_IterGain_root_le
-- name    : GlobalTheory.IterGain.root_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:22:33.246179+00:00
-- url     : https://prove2.me/theorems/eb809cec-a8d7-4062-ae6f-cc0ac5d300cb
-- title:
--   Iter Gain: root le
-- statement:
--   The Iter Gain construction uses the root le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecay.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecay.lean#L33-L34

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

theorem GlobalTheory.IterGain.root_le {x y : ℝ} {m : ℕ} (hm : m ≠ 0) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ m ≤ y ^ m) :
    x ≤ y := by sorry
