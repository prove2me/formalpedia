-- Prove2me | Theorems.Thm_GlobalTheory_RootNormBound_pow_card_le_norm_prod
-- name    : GlobalTheory.RootNormBound.pow_card_le_norm_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:44.100867+00:00
-- url     : https://prove2.me/theorems/e849b9af-121f-464f-a6bd-8f60f06749de
-- title:
--   Root Norm Bound: pow card le norm prod
-- statement:
--   The Root Norm Bound construction uses the pow card le norm prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/PowCardLeNormProd.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/PowCardLeNormProd.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RootNormBound
open Polynomial

theorem GlobalTheory.RootNormBound.pow_card_le_norm_prod {ε : ℝ} (hε : 0 ≤ ε) (s : Multiset ℂ)
    (hs : ∀ t ∈ s, ε ≤ ‖t‖) :
    ε ^ Multiset.card s ≤ ‖(s.map (fun a => (0 : ℂ) - a)).prod‖ := by sorry
