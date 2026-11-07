-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_theorem_1
-- name    : OnlineBudgetAlloc.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:17.791311+00:00
-- url     : https://prove2.me/theorems/6e92ce0f-9ed8-46d0-82bb-444efe92d92d
-- title:
--   Theorem 1 — every randomized online algorithm earns at most $(1 - 1/e - \varepsilon)\,\mathrm{OPT}$ on some unit-budget input
-- statement:
--   Consider online budgeted allocation with $N$ advertisers: items arrive one at a time, advertiser $j$ bids $b_{ij} \ge 0$ on item $i$, and assigning item $i$ to $j$ earns $\min(b_{ij}, R_j)$, where $R_j$ is $j$'s remaining budget. $\mathrm{OPT}(\sigma)$ is the best offline revenue of an input $\sigma$.
--
--   **Theorem 1.** There are constants $\varepsilon > 0$ and $N_0$ such that, for every integer $N \ge N_0$ and every randomized online algorithm $A$ for $N$ advertisers, there is an input $\sigma$ with the following properties: every advertiser has budget $1$, every bid lies in $\{0, \tfrac12, \tfrac34, 1\}$, $\mathrm{OPT}(\sigma) > 0$, and
--   $$
--   \mathbb E[\mathrm{ALG}_A(\sigma)] \le \Bigl(1 - \frac1e - \varepsilon\Bigr)\mathrm{OPT}(\sigma).
--   $$
--
--   So the randomized competitive ratio of online budgeted allocation is at most $1 - 1/e - \varepsilon$, which refutes the conjecture that it equals $1 - 1/e$.
--
--   **Formalization Note** A randomized online algorithm is any probability space with a deterministic online algorithm for each outcome, every decision measurable. The input $\sigma$ is chosen after $N$ and the algorithm, and its number of items is part of the choice.
--
--   Differences from the source:
--   - reading: some fixed input $\sigma$ satisfies $\mathbb E[\mathrm{ALG}_A(\sigma)] \le (1 - 1/e - \varepsilon)\,\mathrm{OPT}(\sigma)$ → the input also satisfies $0 < \mathrm{OPT}(\sigma)$; reason: read literally, an input with no items or all bids $0$ satisfies the inequality ($0 \le 0$) for every algorithm; the theorem bounds the competitive ratio $\mathbb E[\mathrm{ALG}]/\mathrm{OPT}$, which needs $\mathrm{OPT} > 0$, and the paper's inputs have $\mathrm{OPT} = 11N/12 > 0$ (Lemma 2)
--   - generalization: a randomized online algorithm, by Yao's principle a distribution over deterministic online algorithms → any probability space $(\Omega, \mu)$ with a deterministic online algorithm $A_\omega$ per outcome, every decision measurable in $\omega$; algorithms may also use the number of items $m$; reason: covers every finitely supported distribution and every coin-flipping algorithm; an algorithm that ignores $m$ is a special case
--   - encoding: items $1, \dots, M$, advertisers $1, \dots, N$; an item may be left unassigned → zero-based `Fin m`, `Fin N`; `none` = unassigned; bids $\in \{0, 1/2, 3/4, 1\}$ as a `Set ℝ`; reason: Lean convention; same instances
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.2, Theorem 1

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Instance
import Definitions.Def_OnlineBudgetAlloc_revenue
import Definitions.Def_OnlineBudgetAlloc_opt
import Definitions.Def_OnlineBudgetAlloc_DetAlg
import Definitions.Def_OnlineBudgetAlloc_RandAlg

namespace OnlineBudgetAlloc

/-- **Theorem 1** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.2). There are constants `ε > 0` and `N₀` such that, for every
integer `N ≥ N₀` and every randomized online algorithm `A`, some fixed input `σ` on `N` unit-budget
advertisers with bids in `{0, 1/2, 3/4, 1}` satisfies `E[ALG_A(σ)] ≤ (1 − 1/e − ε)·OPT(σ)`.

**Formalization Note**
* The input also satisfies `0 < OPT(σ)`. Without it the statement holds trivially (an input with
  no items, or with all bids `0`, has `E[ALG] = OPT = 0`); the theorem is a bound on the
  competitive ratio `E[ALG]/OPT`, which needs `OPT > 0`.
* A randomized online algorithm is any probability space `(Ω, μ)` with a deterministic online
  algorithm `A ω` for each outcome, every decision measurable in `ω` (`RandAlg`). This covers
  every distribution over deterministic algorithms (Yao's principle, §2, p.2).
* `σ` may depend on `N` and on the algorithm, and is chosen after both; the number of items `m`
  is part of the input. Items and advertisers are zero-based, `none` = unassigned.
* `N` ranges over all integers `≥ N₀`, not only over multiples of the construction's period. -/
theorem theorem_1 :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ R : RandAlg N,
      ∃ (m : ℕ) (σ : Instance N m), (∀ j, σ.B j = 1) ∧
        (∀ i j, σ.b i j ∈ ({0, 1 / 2, 3 / 4, 1} : Set ℝ)) ∧
        0 < opt σ ∧ R.expAlg σ ≤ (1 - 1 / Real.exp 1 - ε) * opt σ := by sorry

end OnlineBudgetAlloc
