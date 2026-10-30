-- Prove2me | Theorems.Thm_LLMThroughput_TokenBudget_theorem_2_b
-- name    : LLMThroughput.TokenBudget.theorem_2_b
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T13:42:13.787533+00:00
-- url     : https://prove2.me/theorems/71327c15-d3ee-4ef5-9d78-51aadd14a9bf
-- title:
--   Theorem 2(b), pp. 15–16 (corrected) — below load b_max/t_{b_max} every work-conserving K-FCFS scheduler has finite expected return time to a finite set
-- statement:
--   Consider the basic LLM queueing model of §3.1: the batch processing time is $t_b=c+a\lceil b/b_0\rceil$ (Assumption 1, $b_0\mid b_{\max}$, $t_{b_{\max}}\ge 1$); the arrival counts $a_n$ per slot are i.i.d. with finite mean $\lambda$; the request sizes $(v_p(i),v_d(i))$ are i.i.d., independent of the arrivals, with values in $[1,v_p^{\max}]\times[1,v_d^{\max}]$ and means $m_p,m_d$. Write $|X(n)|=\sum_{i\in Q_n}(P_i(n)+D_i(n))$ for the total number of unprocessed tokens at the beginning of slot $n$.
--
--   **Theorem 2(b) (stability, corrected).** If
--   $$
--   \lambda(m_p+m_d)<\frac{b_{\max}}{t_{b_{\max}}},
--   $$
--   then for every $K$ and every work-conserving K-FCFS scheduling algorithm there is a finite set $F$ of configurations such that, for every admissible initial state whose requests have at most $v_p^{\max}$ unprocessed prefill and at most $v_d^{\max}$ unprocessed decode tokens, the first time $n\ge 1$ at which the configuration lies in $F$ has finite expectation. A configuration is the remaining batch time together with the token counts $(P_i,D_i)$ of the requests in arrival order, labels forgotten.
--
--   This is part (b) of Theorem 2 of the source in the corrected form used by the mission's goal theorem (finite expected return to a finite set is Foster's form of positive recurrence; the labelled process itself is not positive recurrent).
--
--   **Formalization Note** This is the second conjunct of `LLMThroughput.TokenBudget.theorem_2`, with the load hypothesis moved before the quantifiers. The set $F$ is chosen before the initial state; the expectation is the lower Lebesgue integral of the hitting time in $\mathbb N\cup\{\infty\}$, so a time that is infinite with positive probability has infinite expectation.
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, pp. 15–16, Theorem 2(b) (eqs. (11)–(12)); proof App. B.4, pp. 42–45

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model

namespace LLMThroughput.TokenBudget

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem theorem_2_b {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Params) (hP : P.Valid) (vpmax vdmax : ℕ) (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ)
    (hA : IIDArrivals μ a v vpmax vdmax)
    (hload : arrivalRate μ a * (meanPrefill μ v + meanDecode μ v) < (P.bmax : ℝ) / (P.t P.bmax : ℝ)) :
    ∀ (K : ℕ) (π : Policy), IsScheduler P π → IsWorkConserving P π → IsKFCFS P K π →
      ∃ F : Finset (ℕ × List (ℕ × ℕ)), ∀ x : State, Admissible P.bmax x →
        (∀ r ∈ x.reqs, r.P ≤ vpmax ∧ r.D ≤ vdmax) →
        ∫⁻ ω, ((hitTime F (run P π x (fun m => a m ω) (fun i => v i ω)) : ℕ∞) : ℝ≥0∞) ∂μ
          < ⊤ := by sorry

end LLMThroughput.TokenBudget
