-- Prove2me | Theorems.Thm_GlobalTheory_expSeries_contDiff_and_hasDerivAt
-- name    : GlobalTheory.expSeries_contDiff_and_hasDerivAt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:29.054104+00:00
-- url     : https://prove2.me/theorems/82809954-41b9-4b12-b00f-e66bd2cf96f9
-- title:
--   Global Theory: exp Series cont Diff and has Deriv At
-- statement:
--   The Global Theory construction uses the exp Series cont Diff and has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExpSeriesContDiffAndHasDerivAt.lean#L103-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExpSeriesContDiffAndHasDerivAt.lean#L103-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory
open scoped ContDiff

theorem GlobalTheory.expSeries_contDiff_and_hasDerivAt :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (I : Type) (c : I → ℂ)
      (m : I → V →L[ℝ] ℂ), (∀ R : ℝ, Summable fun i => ‖c i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ ∞ (fun v : V => ∑' i, c i * Complex.exp (m i v)) ∧
        ∀ z : V, Summable (fun i => c i * m i z) ∧
          HasDerivAt (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z)))
            (∑' i, c i * m i z) 0 := by sorry
