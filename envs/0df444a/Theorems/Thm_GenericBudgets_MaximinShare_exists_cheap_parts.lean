-- Prove2me | Theorems.Thm_GenericBudgets_MaximinShare_exists_cheap_parts
-- name    : GenericBudgets.MaximinShare.exists_cheap_parts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:47.516991+00:00
-- url     : https://prove2.me/theorems/77c2d50e-2a74-4b10-b5d5-1dd938936bf3
-- title:
--   Proof of Proposition 3.2 — ℓ inexpensive parts of a partition
-- statement:
--   Let $T_1,\ldots,T_d$ partition a finite set of items, where $d>0$, and let $0\le\ell\le d$. For any real item prices, write $P=\sum_{j\in M}p_j$. There is a set $L$ of exactly $\ell$ part indices such that
--
--   $$
--   p\!\left(\bigcup_{t\in L}T_t\right)\le\frac{\ell}{d}P.
--   $$
--
--   This is the finite averaging fact used to compare a maximin choice with an agent's budget.
--
--   **Formalization Note** Parts may be empty, and the conclusion holds even for negative item prices. In the competitive-equilibrium application prices are nonnegative and $P\le1$.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 9, proof of Proposition 3.2, sentences 3–4

import Mathlib
import Definitions.Def_GenericBudgets_MaximinShare_Setting

namespace GenericBudgets.MaximinShare

/-- Proof of Proposition 3.2, p. 9: some `ℓ` parts cost at most their proportional
share of the total. This averaging statement permits negative prices as well. -/
theorem exists_cheap_parts {m d : ℕ} (p : Fin m → ℝ)
    (T : Fin m → Fin d) (ℓ : ℕ) (hd : 0 < d) (hℓ : ℓ ≤ d) :
    ∃ L : Finset (Fin d), L.card = ℓ ∧
      GenericBudgets.AlmostEqual.price p (partsUnion T L) ≤ ((ℓ : ℝ) / d) * GenericBudgets.AlmostEqual.price p Finset.univ := by sorry

end GenericBudgets.MaximinShare
