-- Prove2me | Theorems.Thm_LLMThroughput_TokenBudget_theorem_2
-- name    : LLMThroughput.TokenBudget.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:44.052304+00:00
-- url     : https://prove2.me/theorems/4efe793a-59b2-4258-9ea0-e91f7db2d0fe
-- title:
--   Theorem 2, pp. 15–16 (corrected: positive recurrence of the label-free configuration) — above load b_max/t_{b_max} every scheduler diverges; below it every work-conserving K-FCFS scheduler is stable
-- statement:
--   **Throughput optimality of work-conserving scheduling.** Consider the basic LLM queueing model. The batch processing time is $t_b=c+a\lceil b/b_0\rceil$ under Assumption 1, with $t_{b_{\max}}\ge 1$. The arrival counts $a_n$ are i.i.d. with finite mean $\lambda$. The request sizes $(v_p(i),v_d(i))$ are i.i.d., independent of the arrivals, take values in $[1,v_p^{\max}]\times[1,v_d^{\max}]$, and have means $m_p,m_d$. Write $|X(n)|=\sum_{i\in Q_n}(P_i(n)+D_i(n))$ for the total number of unprocessed tokens.
--
--   1. **Instability.** If
--      $$
--      \lambda(m_p+m_d)>\frac{b_{\max}}{t_{b_{\max}}},
--      $$
--      then for every scheduling algorithm and every admissible initial state,
--      $$
--      \mathbb P\Big\{\lim_{n\to\infty}|X(n)|=\infty\Big\}=1 .
--      $$
--   2. **Stability.** If
--      $$
--      \lambda(m_p+m_d)<\frac{b_{\max}}{t_{b_{\max}}},
--      $$
--      then for every $K$ and every work-conserving K-FCFS scheduling algorithm there is a finite set $F$ of configurations with the following property. For every admissible initial state whose requests have at most $v_p^{\max}$ unprocessed prefill and at most $v_d^{\max}$ unprocessed decode tokens each, the first time $n\ge 1$ at which the configuration lies in $F$ has finite expectation. A configuration is the remaining batch time together with the token counts $(P_i,D_i)$ of the requests in arrival order, with the labels forgotten.
--
--   The threshold $b_{\max}/t_{b_{\max}}$ is the largest token processing rate of any schedule. Below it, every work-conserving K-FCFS algorithm keeps the system stable, so these algorithms are throughput-optimal; above it, nothing can.
--
--   **Formalization Note** Slots are 0-based. The policy is a function of the current state, labels included, and is required to be feasible (and, in part 2, work-conserving and K-FCFS) at every admissible state. In part 2 the set $F$ is chosen before the initial state. The expectation is the Lebesgue integral of the hitting time in $\mathbb N\cup\{\infty\}$, so a time that is infinite with positive probability has infinite expectation. The boundary case $\lambda(m_p+m_d)=b_{\max}/t_{b_{\max}}$ is not covered, as in the source.
--
--   Differences from the source:
--   - correction: part (b), "the DTMC $\{X(n)\}$ is positive recurrent" → there is a finite set $F$ of label-free configurations (remaining time and the token counts in label order) whose hitting time has finite expectation from every admissible initial state with size-bounded requests; reason: as printed the claim is false for the labelled state (5). With $a_n\equiv 1$, $v\equiv(1,1)$, $c=0$, $a=1$, $b_0=b_{\max}=4$ (load $2<4$) and Sarathi-Serve (work-conserving and K-FCFS with $K=1$), $X(n+1)$ contains the request labelled $n$ and no larger label, so no state recurs. The labelled process is not even Markov once the newest request has departed. The configuration process is the chain the paper's Foster–Lyapunov argument (p. 45) works with, and finite expected return to a finite set is Foster's form of positive recurrence
--   - generalization: the initial state in the paper's state space $\mathcal X$ → in part (a) any admissible state, in part (b) any admissible state whose requests satisfy $P_i\le v_p^{\max}$, $D_i\le v_d^{\max}$, with the policy's defining conditions required at every admissible state; reason: $\mathcal X$ consists of admissible states whose requests obey the paper's size bounds ($v_p(i)\le v_p^{\max}$, $v_d(i)\le v_d^{\max}$ for all $i$), and runs from $\mathcal X$ stay in $\mathcal X$. A policy defined on $\mathcal X$ extends to all admissible states (e.g. greedy oldest-first off $\mathcal X$), which is feasible, work-conserving and K-FCFS with $K=1$. The size bound cannot be dropped in part (b): with $a_n\equiv 0$ ($\lambda=0$), $b_{\max}\ge 2$ and a work-conserving policy that idles whenever the supply (9) is below $b_{\max}$, a single initial request with $P=0$ and $D=N$ never moves, so no finite $F$ serves every $N$
--   - generalization: the policy is a function of the labelled state (5) → a function of the state (5) together with the next arrival label; reason: more policies are covered, and the paper's policies ignore the extra field
--   - encoding: feasibility (6a)–(6d) → (6a)–(6d) plus $\delta^d_i\le D_i$; reason: implicit in "unprocessed decode tokens"
--   - encoding: $a,c\ge 0$ real, $b_0\mid b_{\max}$ → $a,c\in\mathbb N$ and $1\le b_0$, $1\le b_{\max}$, $1\le t_{b_{\max}}$; reason: integer slots force integer $a,c$, and the other conditions only exclude cases where $\lceil b/b_0\rceil$ or $b_{\max}/t_{b_{\max}}$ is undefined
--   - encoding: two independent i.i.d. sequences with $\lambda=E[a_1]$ → measurable maps, `iIndepFun` and `IdentDistrib` within each sequence, the sequences independent as random elements of $\mathbb N^{\mathbb N}$ and $(\mathbb N^2)^{\mathbb N}$, and $a_1$ integrable; reason: the same assumptions in Lean's vocabulary. $\lambda$ is finite in the paper (p. 42)
--   - encoding: slots $1,2,\dots$ and request indices $1,2,\dots$ → 0-based slots and labels, with the state carrying the next label; reason: Lean convention; same instances
--   - encoding: $\lim_{n\to\infty}|X(n)|=\infty$ almost surely → `∀ᵐ ω, Tendsto |X(n)| atTop atTop`; reason: same statement
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, pp. 15–16, Theorem 2 (eqs. (10)–(12)); model §3.1 pp. 12–14, Assumption 1 p. 11, work-conserving and K-FCFS p. 15

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model

namespace LLMThroughput.TokenBudget

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Params) (hP : P.Valid) (vpmax vdmax : ℕ) (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ)
    (hA : IIDArrivals μ a v vpmax vdmax) :
    -- (a) instability under every scheduling algorithm
    ((P.bmax : ℝ) / (P.t P.bmax : ℝ) < arrivalRate μ a * (meanPrefill μ v + meanDecode μ v) →
      ∀ π : Policy, IsScheduler P π → ∀ x : State, Admissible P.bmax x →
        ∀ᵐ ω ∂μ, Tendsto
          (fun n => totalTokens (run P π x (fun m => a m ω) (fun i => v i ω) n)) atTop atTop) ∧
    -- (b) stability under every work-conserving K-FCFS algorithm
    (arrivalRate μ a * (meanPrefill μ v + meanDecode μ v) < (P.bmax : ℝ) / (P.t P.bmax : ℝ) →
      ∀ (K : ℕ) (π : Policy), IsScheduler P π → IsWorkConserving P π → IsKFCFS P K π →
        ∃ F : Finset (ℕ × List (ℕ × ℕ)), ∀ x : State, Admissible P.bmax x →
          (∀ r ∈ x.reqs, r.P ≤ vpmax ∧ r.D ≤ vdmax) →
          ∫⁻ ω, ((hitTime F (run P π x (fun m => a m ω) (fun i => v i ω)) : ℕ∞) : ℝ≥0∞) ∂μ
            < ⊤) := by sorry

end LLMThroughput.TokenBudget
