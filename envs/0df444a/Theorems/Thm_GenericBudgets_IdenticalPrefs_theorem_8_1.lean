-- Prove2me | Theorems.Thm_GenericBudgets_IdenticalPrefs_theorem_8_1
-- name    : GenericBudgets.IdenticalPrefs.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:19.972963+00:00
-- url     : https://prove2.me/theorems/05efd319-d8c8-4475-aeac-65963426c5dd
-- title:
--   Theorem 8.1 — two agents with identical additive preferences and generic unequal budgets have a CE giving truncated shares
-- statement:
--   Consider two agents who share the same standard (additive, normalized, non-negative, monotone, strict) valuation $v_1 = v_2$ over $m$ indivisible items, and unequal budgets $b_1 > b_2 > 0$ with $b_1 + b_2 = 1$. Suppose that for some agent $i$ the budget pair $(b_1, b_2)$ does not belong to the zero-measure set $R_i(v_1, v_2)$ of Definition 6.2. Then there exist an allocation $\mathcal S$ and non-negative item prices $p$ such that $(\mathcal S, p)$ is a competitive equilibrium and every agent gets her truncated share:
--   $$\exists\,(\mathcal S, p) \text{ CE}: \qquad v_j(\mathcal S_j) \ge b_j^- \quad (j = 1, 2).$$
--
--   Here $b_j^-$ is the largest value agent $j$ obtains in a Pareto optimal allocation that gives her at most her budget share $b_j$. With equal budgets a CE can fail to exist even for one item; the theorem shows that for identical preferences, all budget pairs except finitely many have a CE, and that this CE is as fair as the indivisibility allows. It is the formal version of the paper's Theorem 1.4.
--
--   **Formalization Note** Agents are indexed $0, 1$ for the paper's $1, 2$, so $b_1 > b_2$ is `b 1 < b 0`. Identical preferences are `v 0 = v 1` together with the standing assumptions on each valuation. "Does not belong to $R_i$ for some agent $i$" is $\exists i,\ (b_1,b_2) \notin R_i$, not $\forall i$. Strictness is injectivity of the valuation on bundles: the paper's exception allowing identical items is dropped, so markets with identical items are not covered. The truncated share is a maximum over Pareto optimal allocations only.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 20, Theorem 8.1 (formal version of Theorem 1.4, p. 4)

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.IdenticalPrefs

theorem theorem_8_1 {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, GenericBudgets.AlmostEqual.IsStandardValuation (v i)) (hsame : v 0 = v 1)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1) (hlt : b 1 < b 0)
    (hR : ∃ i, ¬ GenericBudgets.AlmostEqual.InR v b i) :
    ∃ (σ : Fin m → Fin 2) (p : Fin m → ℝ), GenericBudgets.AlmostEqual.IsCE v b σ p ∧ ∀ i, GenericBudgets.AlmostEqual.GetsTruncatedShare v b σ i := by sorry

end GenericBudgets.IdenticalPrefs
