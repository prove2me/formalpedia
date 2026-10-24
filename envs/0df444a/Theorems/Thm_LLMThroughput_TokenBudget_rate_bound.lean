-- Prove2me | Theorems.Thm_LLMThroughput_TokenBudget_rate_bound
-- name    : LLMThroughput.TokenBudget.rate_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:29.178365+00:00
-- url     : https://prove2.me/theorems/eac3ef89-0c36-4e7b-a2ca-f802720a8ec9
-- title:
--   Proof sketch of Theorem 2(a), p. 16 (corrected: rates nondecreasing, not strictly increasing) — b/t_b ≤ b_max/t_{b_max} for every token load 1 ≤ b ≤ b_max
-- statement:
--   **Maximal token processing rate.** Let $t_b=c+a\lceil b/b_0\rceil$ be the batch processing time of eq. (4). Here $a,c\ge 0$ are integers, the block size $b_0\ge 1$ divides the token budget $b_{\max}\ge 1$ (Assumption 1), and $t_{b_{\max}}\ge 1$. Then every token load $1\le b\le b_{\max}$ satisfies
--   $$
--   \frac{b}{t_b}\le \frac{b_{\max}}{t_{b_{\max}}}.
--   $$
--
--   The ratio $b/t_b$ is the rate at which a batch of load $b$ processes tokens. The inequality says that full batches are the fastest, so $b_{\max}/t_{b_{\max}}$ is the largest token processing rate of any schedule. It is the threshold of Theorem 2.
--
--   **Formalization Note** The parameters $a$ and $c$ are natural numbers because slots are integers. $\lceil b/b_0\rceil$ is $(b+b_0-1)/b_0$ in natural-number division, and the rates are real quotients.
--
--   Differences from the source:
--   - correction: the step-endpoint rates $kb_0/(c+ak)$ are strictly increasing in $k$ → only the maximum statement $b/t_b\le b_{\max}/t_{b_{\max}}$ is asserted; reason: the strict claim is false when $c=0$ (e.g. $c=0$, $a=1$, $b_0=1$, $b_{\max}=2$: both rates equal $1$), while the maximum statement holds for all $c\ge 0$
--   - reading: "at most $b_{\max}/t_{b_{\max}}$ tokens can be processed per unit time under any algorithm" → stated per batch here; reason: the time-aggregated form is the separate milestone eq. (43) (corrected)
--   - encoding: $a,c\ge 0$ real with integer-valued slots → $a,c\in\mathbb N$; reason: $t_0=c$ and $t_{b_0}-t_0=a$ must be whole numbers of slots, so the instances coincide
--   - encoding: $b_0\mid b_{\max}$ with $\lceil b/b_0\rceil$ and the rate $b_{\max}/t_{b_{\max}}$ → hypotheses $1\le b_0$, $1\le b_{\max}$, $1\le t_{b_{\max}}$; reason: these only exclude cases where the formula or the rate is undefined
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, p. 16, proof sketch of Theorem 2(a); eq. (4) p. 10, Assumption 1 p. 11

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model

namespace LLMThroughput.TokenBudget

theorem rate_bound (P : Params) (hP : P.Valid) (b : ℕ) (hb1 : 1 ≤ b) (hb : b ≤ P.bmax) :
    (b : ℝ) / (P.t b : ℝ) ≤ (P.bmax : ℝ) / (P.t P.bmax : ℝ) := by sorry

end LLMThroughput.TokenBudget
