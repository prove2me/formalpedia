-- Prove2me | Theorems.Thm_LLMThroughput_TokenBudget_eq_43
-- name    : LLMThroughput.TokenBudget.eq_43
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:41.837905+00:00
-- url     : https://prove2.me/theorems/bbeb30fa-2e00-4384-8075-9f1c94d4cb5f
-- title:
--   Eq. (43), App. B.1, p. 38 (corrected: one extra b_max for the batch straddling n_1 t_{b_max}) — cumulative processed tokens grow by at most (n_2 − n_1 + 1) b_max
-- statement:
--   **Cumulative processing bound.** Consider the basic LLM queueing model under any scheduling algorithm $\pi$ and from any admissible initial state. Let the arrival counts and the request sizes be arbitrary, with every size at least $1$. For a phase $f\in\{p,d\}$, let $B_f(n)$ be the number of phase-$f$ tokens in the batches that the algorithm formed and that completed by time $n$. Then for all $n_1<n_2$,
--   $$
--   B_f\big(n_2 t_{b_{\max}}\big)-B_f\big(n_1 t_{b_{\max}}\big)\le (n_2-n_1+1)\,b_{\max},\qquad f\in\{p,d\}.
--   $$
--
--   The bound makes precise that no schedule processes more than $b_{\max}$ tokens per $t_{b_{\max}}$ slots, apart from one batch straddling the left end of the window. It gives the Lipschitz bound of the fluid model (eq. (47)) after fluid scaling.
--
--   **Formalization Note** Slots are 0-based, and "by time $n$" means by the end of slot $n-1$, which is the paper's slot $n$. A batch formed in slot $m$ with processing time $t_b>0$ is counted in $B_f(n)$ once $m+t_b\le n$. The bound is written as $B_f(n_2t_{b_{\max}})\le B_f(n_1t_{b_{\max}})+(n_2-n_1+1)b_{\max}$, which avoids natural-number subtraction.
--
--   Differences from the source:
--   - correction: $(n_2-n_1)\,b_{\max}$ → $(n_2-n_1+1)\,b_{\max}$; reason: the printed bound is false. Take $c=1$, $a=1$, $b_0=1$, $b_{\max}=2$ (so $t_1=2$, $t_2=t_{b_{\max}}=3$), no arrivals, and an initial state with $R=1$ and one request with $3$ prefill tokens and $1$ decode token. A work-conserving run forms a full batch of $2$ tokens in the paper's slot $2$, which completes at the end of slot $4$, and then a 1-token batch, which completes at the end of slot $6$. So $B_p(6)-B_p(3)=3>2$
--   - reading: $B_f(n)$, "the cumulative number of tokens that have been completed phase $f$ processing by time $n$" → phase-$f$ tokens of batches formed during the run and completed by time $n$; reason: the composition of a batch already in progress in the initial state is not part of the state (5), so its tokens cannot be counted
--   - generalization: $n_1,n_2\in\{1,2,\dots\}$ → $n_1,n_2\in\{0,1,\dots\}$; reason: covers more instances and specializes to the source's
--   - generalization: initial state in the paper's state space $\mathcal X$ → any admissible state, with feasibility required at every admissible state; reason: $\mathcal X$ consists of admissible states. A scheduling algorithm defined on $\mathcal X$ extends feasibly to all admissible states (e.g. greedy oldest-first off $\mathcal X$), and a run from a state of $\mathcal X$ never leaves $\mathcal X$
--   - generalization: the policy is a function of the labelled state (5) → a function of the state (5) together with the next arrival label; reason: more policies are covered, and the paper's policies are those that ignore the extra field
--   - generalization: random i.i.d. sizes bounded by $v^{\max}$ → arbitrary deterministic arrival counts and sizes $\ge 1$, no upper bound; reason: the statement holds pathwise, so it specializes to every sample path of the paper's model
--   - encoding: feasibility (6a)–(6d) → (6a)–(6d) plus $\delta^d_i\le D_i$; reason: a request has no decode token left to contribute when $D_i=0$, which is implicit in "unprocessed decode tokens"
--   - encoding: $a,c\ge 0$ real, $b_0\mid b_{\max}$ → $a,c\in\mathbb N$ and $1\le b_0$, $1\le b_{\max}$, $1\le t_{b_{\max}}$; reason: integer slots force integer $a,c$, and the other conditions only exclude undefined cases
--   - encoding: slots $1,2,\dots$ → slots $0,1,\dots$; reason: Lean convention; same instances
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, p. 38, eq. (43), App. B.1 (B_f defined on p. 37)

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model

namespace LLMThroughput.TokenBudget

theorem eq_43 (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π)
    (x : State) (hx : Admissible P.bmax x) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ)
    (hv : ∀ i, 1 ≤ (v i).1 ∧ 1 ≤ (v i).2) (n₁ n₂ : ℕ) (hn : n₁ < n₂) :
    completedTokens P π x a v prefillLoad (n₂ * P.t P.bmax)
        ≤ completedTokens P π x a v prefillLoad (n₁ * P.t P.bmax) + (n₂ - n₁ + 1) * P.bmax ∧
      completedTokens P π x a v decodeLoad (n₂ * P.t P.bmax)
        ≤ completedTokens P π x a v decodeLoad (n₁ * P.t P.bmax) + (n₂ - n₁ + 1) * P.bmax := by sorry

end LLMThroughput.TokenBudget
