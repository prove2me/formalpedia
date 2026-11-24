-- Prove2me | Theorems.Thm_GlobalTheory_RootNormPowerBound_pow_card_le_norm_eval_prod
-- name    : GlobalTheory.RootNormPowerBound.pow_card_le_norm_eval_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:42.469587+00:00
-- url     : https://prove2.me/theorems/9b26ada2-d4e1-4535-90ab-0416d2538161
-- title:
--   Root Norm Power Bound: pow card le norm eval prod
-- statement:
--   The Root Norm Power Bound construction uses the pow card le norm eval prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRootNormSubPowLe.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRootNormSubPowLe.lean#L9-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRootNormSubPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.RootNormPowerBound
open Polynomial

theorem GlobalTheory.RootNormPowerBound.pow_card_le_norm_eval_prod {K : Type u_1} [NormedField K] (x : K) (c : ℝ) (hc : 0 ≤ c)
    (s : Multiset K) (hs : ∀ a ∈ s, c ≤ ‖a - x‖) :
    c ^ Multiset.card s ≤ ‖Polynomial.eval x (s.map fun a => X - C a).prod‖ := by sorry
