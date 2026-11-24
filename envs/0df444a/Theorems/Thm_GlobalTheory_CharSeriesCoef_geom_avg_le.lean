-- Prove2me | Theorems.Thm_GlobalTheory_CharSeriesCoef_geom_avg_le
-- name    : GlobalTheory.CharSeriesCoef.geom_avg_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:07:49.35887+00:00
-- url     : https://prove2.me/theorems/11a98869-9a8f-476c-aa1b-1b1545f94f65
-- title:
--   Char Series Coef: geom avg le
-- statement:
--   The Char Series Coef construction uses the geom avg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZero.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZero.lean#L33-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CharSeriesCoef

theorem GlobalTheory.CharSeriesCoef.geom_avg_le {ζ : ℂ} (hζ : ζ ≠ 1) (h1 : ‖ζ‖ = 1) (K : ℕ) (hK : 0 < K) :
    ‖(K:ℂ)⁻¹ * ∑ k : Fin K, ζ ^ (k:ℕ)‖ ≤ 2 / (K * ‖ζ - 1‖) := by sorry
