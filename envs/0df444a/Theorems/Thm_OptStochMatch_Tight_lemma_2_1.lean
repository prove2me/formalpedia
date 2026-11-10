-- Prove2me | Theorems.Thm_OptStochMatch_Tight_lemma_2_1
-- name    : OptStochMatch.Tight.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:58:08.495913+00:00
-- url     : https://prove2.me/theorems/24b77eeb-b681-461c-be6f-8c52ad339ab1
-- title:
--   Lemma 2.1 — online scheduling: expected total work equals expected number of completed jobs
-- statement:
--   For every nonanticipating online scheduling policy on a compact, convex, downward-closed feasible-rate region $P\subseteq\mathbb R^m_+$ containing $0$, with independent demands $Z_i\sim\mathrm{Exp}(1)$,
--   $$\mathbb E\Big[\sum_{i=1}^m x_i(1)\Big]=\mathbb E\Big[\sum_{i=1}^m 1\{x_i(1)=Z_i\}\Big].$$
--
--   Differences from the source:
--   - encoding: nonanticipating scheduling policy (observed history and independent randomization) → SchedPolicy: a jointly measurable rate map of a Uniform[0,1] seed, the completion history and the time, in P, zero on completed jobs; reason: between completions the observed history is the elapsed time and the policy's own service; same policy class
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in ℝ≥0∞; reason: the integrands are nonnegative, so the values agree; no integrability side condition can be vacuous
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Lemma 2.1, p. 7 (PDF p. 8)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Scheduling
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace OptStochMatch.Tight

/-- Lemma 2.1 (p. 7, PDF 8). For every nonanticipating online scheduling policy on a
feasible-rate region `P`, with independent `Exp(1)` service demands, the expected total work
processed by time `1` equals the expected number of completed jobs:
`E[∑_i x_i(1)] = E[∑_i 1{x_i(1) = Z_i}]`. -/
theorem lemma_2_1 {m : ℕ} (P : Set (Fin m → ℝ)) (hP : IsRateRegion P) (σ : SchedPolicy m P) :
    expTotalWork σ = expCompletions σ := by sorry

end OptStochMatch.Tight
