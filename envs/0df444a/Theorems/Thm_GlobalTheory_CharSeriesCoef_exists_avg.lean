-- Prove2me | Theorems.Thm_GlobalTheory_CharSeriesCoef_exists_avg
-- name    : GlobalTheory.CharSeriesCoef.exists_avg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:07:51.48693+00:00
-- url     : https://prove2.me/theorems/f9721ab6-5c43-430d-8435-a560cd407620
-- title:
--   Char Series Coef: exists avg
-- statement:
--   The Char Series Coef construction uses the exists avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZero.lean#L45-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZero.lean#L45-L87

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

theorem GlobalTheory.CharSeriesCoef.exists_avg {Y Ξ : Type} [AddCommGroup Y] [Zero Ξ] (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (δ : ℝ) (hδ : 0 < δ) (T : Finset Ξ) (h0 : (0:Ξ) ∉ T) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (w : ι → Y),
      ∀ b ∈ T, ‖avg w (e b)‖ ≤ δ := by sorry
