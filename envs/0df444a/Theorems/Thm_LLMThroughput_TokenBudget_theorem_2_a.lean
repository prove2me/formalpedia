-- Prove2me | Theorems.Thm_LLMThroughput_TokenBudget_theorem_2_a
-- name    : LLMThroughput.TokenBudget.theorem_2_a
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T13:42:12.703484+00:00
-- url     : https://prove2.me/theorems/31141d95-762a-41d9-9561-cfb2e366122b
-- title:
--   Theorem 2(a), pp. 15–16 — above load b_max/t_{b_max} the token backlog diverges a.s. under every scheduler
-- statement:
--   Consider the basic LLM queueing model of §3.1: the batch processing time is $t_b=c+a\lceil b/b_0\rceil$ (Assumption 1, $b_0\mid b_{\max}$, $t_{b_{\max}}\ge 1$); the arrival counts $a_n$ per slot are i.i.d. with finite mean $\lambda$; the request sizes $(v_p(i),v_d(i))$ are i.i.d., independent of the arrivals, with values in $[1,v_p^{\max}]\times[1,v_d^{\max}]$ and means $m_p,m_d$. Write $|X(n)|=\sum_{i\in Q_n}(P_i(n)+D_i(n))$ for the total number of unprocessed tokens at the beginning of slot $n$.
--
--   **Theorem 2(a) (instability).** If
--   $$
--   \lambda(m_p+m_d)>\frac{b_{\max}}{t_{b_{\max}}},
--   $$
--   then for every (batch) scheduling algorithm and every admissible initial state,
--   $$
--   \mathbb P\Big\{\lim_{n\to\infty}|X(n)|=\infty\Big\}=1 .
--   $$
--
--   This is part (a) of Theorem 2 of the source: $b_{\max}/t_{b_{\max}}$ is the largest token processing rate of any schedule, so above it no algorithm can keep up with the incoming work.
--
--   **Formalization Note** This is the first conjunct of `LLMThroughput.TokenBudget.theorem_2`, with the load hypothesis moved before the quantifiers; slots are 0-based, the policy is a function of the labelled state and is required to be feasible at every admissible scheduling instant, and almost-sure divergence is `∀ᵐ ω, Tendsto |X(n)| atTop atTop`.
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, pp. 15–16, Theorem 2(a) (eq. (10)); proof sketch p. 16 and App. B.3, pp. 41–42

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model

namespace LLMThroughput.TokenBudget

open MeasureTheory ProbabilityTheory Filter Topology

theorem theorem_2_a {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Params) (hP : P.Valid) (vpmax vdmax : ℕ) (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ)
    (hA : IIDArrivals μ a v vpmax vdmax)
    (hload : (P.bmax : ℝ) / (P.t P.bmax : ℝ) < arrivalRate μ a * (meanPrefill μ v + meanDecode μ v)) :
    ∀ π : Policy, IsScheduler P π → ∀ x : State, Admissible P.bmax x →
      ∀ᵐ ω ∂μ, Tendsto
        (fun n => totalTokens (run P π x (fun m => a m ω) (fun i => v i ω) n)) atTop atTop := by sorry

end LLMThroughput.TokenBudget
