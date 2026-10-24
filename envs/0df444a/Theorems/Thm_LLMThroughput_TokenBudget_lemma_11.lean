-- Prove2me | Theorems.Thm_LLMThroughput_TokenBudget_lemma_11
-- name    : LLMThroughput.TokenBudget.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:35.00124+00:00
-- url     : https://prove2.me/theorems/0d5ff29b-36c9-4a8a-8425-e5b46e44ac6c
-- title:
--   Lemma 11, p. 38 (corrected: departure order only; the prefill-completion clause is false) — under work-conserving K-FCFS, a request departs only after every request at least K′ older
-- statement:
--   **Bounded overtaking in departure order.** Fix $K$, the size bounds $v_p^{\max}, v_d^{\max}$ and the token budget $b_{\max}$. Then there is a finite constant $K'$, depending only on these four numbers, with the following property. Take any batch-time parameters $c,a,b_0$ satisfying Assumption 1 and any work-conserving K-FCFS scheduling algorithm. Let requests arrive in arbitrary numbers with sizes $1\le v_p(i)\le v_p^{\max}$ and $1\le v_d(i)\le v_d^{\max}$, into a system that starts empty, with requests labelled $0,1,2,\dots$ in arrival order. Then for all labels $i, j$ with
--   $$
--   i + K' \le j,
--   $$
--   if request $j$ is in the system at the beginning of slot $n$ and departs at the end of slot $n$, then request $i$ departed before slot $n$.
--
--   In words: a request cannot leave the system before every request that arrived at least $K'$ positions earlier has left. Bounded overtaking couples the cumulative token counts with the cumulative completed requests (eq. (44)), which is what the fluid-limit argument needs.
--
--   **Formalization Note** "Departed" means the label has been issued and is no longer in the state. The claim holds for every deterministic sequence of arrival counts and sizes within the bounds, and so for every sample path of the random model. The constant $K'$ is chosen before the batch-time parameters, the algorithm and the sample path.
--
--   Differences from the source:
--   - correction: for each phase $f\in\{p,d\}$ → only $f=d$ (departure order); reason: the prefill clause is false. Take $K=1$, $b_{\max}=b_0=1$, $c=0$, $a=1$ and all sizes $(1,1)$, with $M$ requests arriving in the first slot. The policy "one prefill token of the newest request still in prefill, otherwise one decode token of the oldest request" is a work-conserving K-FCFS scheduling algorithm, and it completes prefill in the order $M,M-1,\dots,1$, so for every $K'$ some request completes prefill before one $K'$ positions older
--   - reading: "request $j$ can complete phase $f$ only if every request $i\le j-K'$ has already completed phase $f$" → if $j$ is present at the start of slot $n$ and gone at the start of slot $n+1$, then $i$ is gone at the start of slot $n$; reason: the strict reading of "already" (before $j$, not in the same batch), which implies the non-strict one
--   - reading: requests indexed $i=1,2,\dots$ by global arrival time, initial state unspecified → the run starts from the empty system and labels its arrivals $0,1,2,\dots$; reason: every state of the paper's state space is reached from the empty system, and a run from such a state continues a run from empty with the arrival sequences concatenated, so the two statements are equivalent. From an arbitrary state with a large gap between the labels of present requests, the conclusion fails
--   - generalization: random i.i.d. arrival counts and sizes → every deterministic sequence of arrival counts and of sizes within the bounds; reason: the statement is pathwise and specializes to every sample path
--   - generalization: the policy is a function of the labelled state (5) → a function of the state (5) together with the next arrival label, with the defining conditions required at every admissible state; reason: more policies are covered, and the paper's policies ignore the extra field and extend from the reachable states
--   - encoding: $i\le j-K$ in the K-FCFS condition and $i\le j-K'$ → $i+K\le j$ and $i+K'\le j$ on 0-based labels; reason: avoids natural-number subtraction; same instances
--   - encoding: feasibility (6a)–(6d) → (6a)–(6d) plus $\delta^d_i\le D_i$; reason: implicit in "unprocessed decode tokens"
--   - encoding: $a,c\ge 0$ real, $b_0\mid b_{\max}$ → $a,c\in\mathbb N$ and $1\le b_0$, $1\le b_{\max}$, $1\le t_{b_{\max}}$; reason: integer slots force integer $a,c$, and the other conditions only exclude undefined cases
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, p. 38, Lemma 11 (App. B.1); K-FCFS condition p. 15

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model

namespace LLMThroughput.TokenBudget

theorem lemma_11 (K vpmax vdmax bmax : ℕ) :
    ∃ K' : ℕ, ∀ (P : Params), P.bmax = bmax → P.Valid →
      ∀ π : Policy, IsScheduler P π → IsWorkConserving P π → IsKFCFS P K π →
      ∀ (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ),
        (∀ i, 1 ≤ (v i).1 ∧ (v i).1 ≤ vpmax ∧ 1 ≤ (v i).2 ∧ (v i).2 ≤ vdmax) →
      ∀ (n i j : ℕ), i + K' ≤ j →
        Present (run P π State.empty a v n) j →
        Departed (run P π State.empty a v (n + 1)) j →
        Departed (run P π State.empty a v n) i := by sorry

end LLMThroughput.TokenBudget
