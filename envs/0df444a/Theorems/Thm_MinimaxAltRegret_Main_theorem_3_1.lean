-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_theorem_3_1
-- name    : MinimaxAltRegret.Main.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:37.575967+00:00
-- url     : https://prove2.me/theorems/4e4762d1-e790-4569-b5ff-17eef0e92d71
-- title:
--   Theorem 3.1 — oblivious experts lower bound
-- statement:
--   Let d>=2 and let T be an integer horizon with T>=log_2 d, where log_2 d=log d/log 2. For every possibly randomized full-information expert learner playing probability vectors in Delta_d, there is a single loss-vector sequence ell_1,...,ell_T in [-1,1]^d, fixed before play, such that
--
--   $$\mathbb E[R_T^{\mathrm{exp}}]\ge\lfloor\log_2d\rfloor.$$
--
--   The expectation is over the learner's private seed, after maximizing over the hindsight comparator. The terminal probability vector is also selected by the same causal learner. This is the lower half of the expert minimax characterization.
--
--   Differences from the source:
--   - encoding: rounds 1 through T and the terminal action x_(T+1) → zero-based losses and actions, with action T terminal and source score R_t stored at index t; reason: a bijective reindexing preserves every summand and includes the same terminal update
--   - encoding: a possibly randomized full-information learner and its internal expectation → an arbitrary probability space, a measurable seed-based HistoryLearner on all finite revealed-loss histories, and an explicitly integrable regret random variable; reason: this gives the stated nonanticipating learner and a genuine bounded expectation, with the hindsight supremum inside the integral
--   - encoding: the maximum of expert comparator regret over the simplex → the real sSup of the same comparator-regret image; reason: for d>=1 the finite simplex is nonempty and compact and the comparator objective is continuous, so the maximum is attained and equals this sSup
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 4 / PDF p. 5, Theorem 3.1; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Experts

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem theorem_3_1 :
  ∀ (d T : ℕ), 2 ≤ d → Real.log (d : ℝ) / Real.log 2 ≤ (T : ℝ) →
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (learner : HistoryLearner (ExpertAction d) (ExpertVector d) Ω),
    ∃ ℓ : ℕ → ExpertVector d, expertLosses d T ℓ ∧
      Integrable (fun ω => expertRegret T ℓ
        (fun t => (response learner ℓ t ω).val)) μ ∧
      (⌊Real.log (d : ℝ) / Real.log 2⌋ : ℤ) ≤
        ∫ ω, expertRegret T ℓ (fun t => (response learner ℓ t ω).val) ∂μ := by sorry

end MinimaxAltRegret.Main
