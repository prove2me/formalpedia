-- Prove2me | Theorems.Thm_GenericBudgets_IdenticalPrefs_lemma_8_2
-- name    : GenericBudgets.IdenticalPrefs.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:32:08.055134+00:00
-- url     : https://prove2.me/theorems/05656b5e-1a97-4863-82e1-49e3145f6a2e
-- title:
--   Lemma 8.2 — if every allocation is PO and the budgets avoid some R_i, a CE exists, with truncated shares when no PO allocation is anti-proportional
-- statement:
--   Consider two agents with standard (additive, normalized, non-negative, monotone, strict) valuations $v_1, v_2$ and budgets $b_1 > b_2 > 0$ with $b_1 + b_2 = 1$, such that for some agent $i$ the budget pair is outside the zero-measure set $R_i(v_1,v_2)$ of Definition 6.2. Suppose every allocation is Pareto optimal. Then there is a competitive equilibrium $(\mathcal S, p)$ such that, moreover, if no Pareto optimal allocation is anti-proportional, this same CE gives every agent her truncated share:
--   $$\Big(\nexists\, \mathcal S' \text{ PO anti-proportional}\Big) \;\Longrightarrow\; v_j(\mathcal S_j) \ge b_j^- \quad (j = 1, 2).$$
--
--   The lemma does not assume identical preferences, only that the Pareto frontier is all allocations. Combined with the constant-sum observation it yields Theorem 8.1.
--
--   **Formalization Note** Agents are indexed $0, 1$, so $b_1 > b_2$ is `b 1 < b 0`. "Does not belong to $R_i$ for some agent $i$" is read as $\exists i,\ (b_1,b_2) \notin R_i$. The existence and the "moreover" part concern one and the same CE, so both sit under a single existential. Valuations are strict without the identical-items exception.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 20, Lemma 8.2

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.IdenticalPrefs

theorem lemma_8_2 {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, GenericBudgets.AlmostEqual.IsStandardValuation (v i))
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1) (hlt : b 1 < b 0)
    (hR : ∃ i, ¬ GenericBudgets.AlmostEqual.InR v b i) (hallPO : ∀ σ, GenericBudgets.AlmostEqual.IsPO v σ) :
    ∃ (σ : Fin m → Fin 2) (p : Fin m → ℝ), GenericBudgets.AlmostEqual.IsCE v b σ p ∧
      ((∀ σ', GenericBudgets.AlmostEqual.IsPO v σ' → ¬ GenericBudgets.AlmostEqual.IsAntiProportional v b σ') → ∀ i, GenericBudgets.AlmostEqual.GetsTruncatedShare v b σ i) := by sorry

end GenericBudgets.IdenticalPrefs
