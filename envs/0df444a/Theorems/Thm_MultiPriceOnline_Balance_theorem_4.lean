-- Prove2me | Theorems.Thm_MultiPriceOnline_Balance_theorem_4
-- name    : MultiPriceOnline.Balance.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:32.654433+00:00
-- url     : https://prove2.me/theorems/7b611628-0e13-4ae3-a062-b393436bc922
-- title:
--   Theorem 4, p. 19 — procedures satisfying (17)–(18) with c make Multi-price Balance c-competitive
-- statement:
--   Consider any setup with a finite set of items: item $i$ has inventory $k_i\ge1$ and prices $0<r_i^{(1)}<\dots<r_i^{(m_i)}$, $m_i\ge1$. In Line 1 of Algorithm 1 (Multi-price Balance), the borders $\tilde L_i^{(j)}$ and the value function $\tilde\Phi_i$ of each item are drawn, independently across items, from a randomized procedure. The procedure satisfies, for a constant $c$,
--   $$
--   k_i\Big(\tilde\Phi_i\big(\tfrac{N+1}{k_i}\big)-\tilde\Phi_i\big(\tfrac N{k_i}\big)\Big)+\tilde\Phi_i\big(\tilde L_i^{(j)}\big)-\tilde\Phi_i\big(\tfrac N{k_i}\big)\le\frac{r_i^{(j)}}{c},\qquad j\in[m_i],\ N\in\{0,\dots,\tilde L_i^{(j)}k_i-1\},\tag{17}
--   $$
--   for every initialization of positive probability, and
--   $$
--   \mathbb E\big[\tilde\Phi_i(\tilde L_i^{(j)})\big]\ge r_i^{(j)},\qquad j\in[m_i].\tag{18}
--   $$
--   Then Algorithm 1 achieves a competitive ratio of $c$. Take any number of customers $T$, any purchase probabilities $p^{(j)}_{t,i}\in[0,1]$, any tie-breaking rule that offers a maximizer of (16), and any feasible solution $x$ of the LP (5). Then
--   $$
--   c\cdot\sum_{t,i,j}p^{(j)}_{t,i}r_i^{(j)}x^{(j)}_{t,i}\ \le\ \mathbb E[\mathrm{ALG}(\mathcal S,\mathcal A)].
--   $$
--
--   This is the paper's reduction of the competitive analysis to a single-item design problem. It is combined with Theorem 5 and the procedure (45) in the proof of Theorem 1.
--
--   **Formalization Note** The competitive ratio (6), $\mathbb E[\mathrm{ALG}]/\mathrm{OPT}\ge c$, is stated multiplied out for every feasible $x$, so that $\mathrm{OPT}=0$ causes no division by zero. The procedures are fixed before the arrival sequence. No positivity of $c$ is assumed, because (17)–(18) already force $c>0$. Take a configuration of positive probability and $j=m_i$. If $c<0$, (17) at $N=0$ would make a nonnegative quantity negative. If $c=0$, Lean reads $r/0$ as $0$, so (17) forces the value function to vanish, contradicting (18).
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 19, Theorem 4, (17)–(18); proof in App. B.1, pp. 39–40

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_LP
import Definitions.Def_MultiPriceOnline_Balance_Procedure
import Definitions.Def_MultiPriceOnline_Balance_Algorithm

namespace MultiPriceOnline.Balance

/-- Theorem 4 (Ma–Simchi-Levi, arXiv:1905.04770v1, p. 19). Suppose that in Line 1 of Algorithm 1
every item `i` is initialized by a randomized procedure `P i` satisfying (17) with constant `c` for
every potential initialization and (18) in expectation. Then Algorithm 1 achieves a competitive
ratio of `c`: for every arrival sequence, every tie-breaking rule maximizing (16) and every feasible
solution `x` of the LP (5), `c · (5a)(x) ≤ 𝔼[ALG]`. -/
theorem theorem_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (k m : ι → ℕ)
    (hk : ∀ i, 1 ≤ k i) (hm : ∀ i, 1 ≤ m i) (r : ι → ℕ → ℝ) (hr : ∀ i, IsPriceSet (m i) (r i))
    (P : ∀ i, Procedure (k i) (m i)) (hP : ∀ i, IsProcedure (P i)) (c : ℝ)
    (h17 : ∀ i, Cond17 (r i) (P i) c) (h18 : ∀ i, Cond18 (r i) (P i))
    {T : ℕ} (p : Fin T → ι → ℕ → ℝ)
    (hp : ∀ t i j, 1 ≤ j → j ≤ m i → 0 ≤ p t i j ∧ p t i j ≤ 1)
    (sel : Selector m) (hsel : IsArgmaxSelector sel)
    (x : Fin T → ι → ℕ → ℝ) (hx : LPFeasible k m p x) :
    c * lpObj m r p x ≤ expRevenue k m r P sel p := by sorry

end MultiPriceOnline.Balance
