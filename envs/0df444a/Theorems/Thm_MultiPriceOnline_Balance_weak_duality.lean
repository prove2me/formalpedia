-- Prove2me | Theorems.Thm_MultiPriceOnline_Balance_weak_duality
-- name    : MultiPriceOnline.Balance.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:54.686092+00:00
-- url     : https://prove2.me/theorems/88eba0bc-d2fd-4692-ab48-807c917a0447
-- title:
--   Weak duality, p. 19 — every feasible solution of the dual (19) bounds the LP (5)
-- statement:
--   Consider the LP (5) of the multi-price online allocation problem: items $i$ with inventories $k_i$ and prices $r_i^{(j)}$, $j\in[m_i]$; customers $t\in[T]$; purchase probabilities $p^{(j)}_{t,i}$. Let $x$ be feasible for (5), i.e. it satisfies (5b)–(5d). Let $(y,z)$ be feasible for its dual (19), i.e. it satisfies (19b)–(19c). Then
--   $$
--   \sum_{t=1}^T\sum_i\sum_{j=1}^{m_i}p^{(j)}_{t,i}r_i^{(j)}x^{(j)}_{t,i}\ \le\ \sum_i k_iy_i+\sum_{t=1}^T z_t.
--   $$
--   In particular $\mathrm{OPT}(\mathcal S,\mathcal A)$ is at most the objective of any dual feasible solution. This is the first step of the primal–dual proof of Theorem 4.
--
--   **Formalization Note** No sign condition on $p$ is assumed; the inequality holds for all real $p$, which is a stronger statement than needed. The same statement is posed in mission II of this series (Multi-price Ranking), because drafts of concurrent missions cannot import each other.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 19, (19a)–(19c) and the sentence after (19c)

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_LP

namespace MultiPriceOnline.Balance

/-- Weak duality for the LP (5) and its dual (19) (Ma–Simchi-Levi, arXiv:1905.04770v1, p. 19, the
sentence after (19c)): the objective (5a) of every feasible solution of (5) is at most the
objective (19a) of every feasible solution of (19). -/
theorem weak_duality {ι : Type*} [Fintype ι] (k m : ι → ℕ) (r : ι → ℕ → ℝ) {T : ℕ}
    (p : Fin T → ι → ℕ → ℝ) (x : Fin T → ι → ℕ → ℝ) (hx : LPFeasible k m p x)
    (y : ι → ℝ) (z : Fin T → ℝ) (hyz : DualFeasible m r p y z) :
    lpObj m r p x ≤ dualObj k y z := by sorry

end MultiPriceOnline.Balance
