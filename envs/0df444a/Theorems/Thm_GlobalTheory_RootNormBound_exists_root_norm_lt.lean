-- Prove2me | Theorems.Thm_GlobalTheory_RootNormBound_exists_root_norm_lt
-- name    : GlobalTheory.RootNormBound.exists_root_norm_lt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:19.42013+00:00
-- url     : https://prove2.me/theorems/0d4f92a3-3451-44da-84fb-91b3e84c114d
-- title:
--   Root Norm Bound: exists root norm lt
-- statement:
--   The Root Norm Bound construction uses the exists root norm lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/PowCardLeNormProd.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/PowCardLeNormProd.lean#L20-L29

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

theorem GlobalTheory.RootNormBound.exists_root_norm_lt {h : Polynomial ℂ} (hm : h.Monic) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ‖h.coeff 0‖ < ε ^ h.natDegree) : ∃ t : ℂ, h.IsRoot t ∧ ‖t‖ < ε := by sorry
