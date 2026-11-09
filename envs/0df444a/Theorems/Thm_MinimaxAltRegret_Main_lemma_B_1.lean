-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_lemma_B_1
-- name    : MinimaxAltRegret.Main.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:51.437137+00:00
-- url     : https://prove2.me/theorems/6ff6c1f5-d4d5-495f-a605-5af268e9bab7
-- title:
--   Lemma B.1 — a universal oblivious distribution on the disk
-- statement:
--   Let D be the closed unit Euclidean disk in R^2 and fix c_0=1/(80 log 65536)>0. For every integer T>=5, there is one finitely supported distribution P_T on complete sequences of continuous convex losses D to [0,1], selected before any learner, such that every possibly randomized history-based learner satisfies
--
--   $$\mathbb E_{f_{1:T}\sim P_T,\,\mathrm{seed}}[R_T]\ge c_0\log T.$$
--
--   The environment outcome and learner seed are independent: the formal expectation is the finite weighted sum of the seed expectations for the fixed sequences. Each regret random variable is integrable. The same P_T works for every learner, including deterministic learners, and includes their terminal actions. This is the two-dimensional ingredient for the general OCO lower bound.
--
--   **Formalization Note** The constant is the instantiation from (40)--(43), with delta_1=1/8 and r=1/4096. The finite distribution and continuity of its losses are properties of the paper's construction, not extra learner hypotheses.
--
--   Differences from the source:
--   - encoding: rounds 1 through T and the terminal action x_(T+1) → zero-based losses and actions, with action T terminal and source score R_t stored at index t; reason: a bijective reindexing preserves every summand and includes the same terminal update
--   - encoding: a possibly randomized full-information learner and its internal expectation → an arbitrary probability space, a measurable seed-based HistoryLearner on all finite revealed-loss histories, and an explicitly integrable regret random variable; reason: this gives the stated nonanticipating learner and a genuine bounded expectation, with the hindsight supremum inside the integral
--   - generalization: there exists a positive universal constant and an oblivious distribution of convex [0,1] losses → c_0=1/(80 log 65536), with a single finitely supported distribution of continuous convex [0,1] losses before all learners; reason: the proof uses finitely many Bernoulli outcomes at any fixed horizon and the continuous functions (27),(28), and (42),(43) give this explicit constant
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 16 / PDF p. 17, Lemma B.1, Eq. (26); proof Eqs. (29), (40)--(43); SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Sampling
import Definitions.Def_MinimaxAltRegret_Main_LowerConstruction

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem lemma_B_1 :
    0 < diskConstant ∧ ∀ T : ℕ, 5 ≤ T →
      ∃ (N : ℕ) (env : FiniteEnvironment (Point 2 → ℝ) N), 0 < N ∧
        (∀ j, continuousLosses01 unitDisk T (env.sequence j)) ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (learner : HistoryLearner unitDisk (Point 2 → ℝ) Ω),
          (∀ j, Integrable (fun ω => alternatingRegret unitDisk T (env.sequence j)
            (fun t => (response learner (env.sequence j) t ω).val)) μ) ∧
          diskConstant*Real.log (T : ℝ) ≤
            ∑ j, env.weight j * ∫ ω, alternatingRegret unitDisk T (env.sequence j)
              (fun t => (response learner (env.sequence j) t ω).val) ∂μ := by sorry

end MinimaxAltRegret.Main
