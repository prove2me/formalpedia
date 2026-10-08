-- Prove2me | Theorems.Thm_GenericBudgets_IdenticalPrefs_proposition_5_1
-- name    : GenericBudgets.IdenticalPrefs.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:07.314259+00:00
-- url     : https://prove2.me/theorems/ffbd6776-86a8-4a75-bf7e-82b944564d3b
-- title:
--   Proposition 5.1 — budget-proportional and anti-proportional PO allocations are supported in a CE
-- statement:
--   Consider two agents with standard (additive, normalized, non-negative, monotone, strict) valuations $v_1, v_2$ on $m$ indivisible items, and positive budgets $b_1, b_2$ with $b_1 + b_2 = 1$. Let $\mathcal S$ be a Pareto optimal allocation. Then:
--
--   1. if $\mathcal S$ is budget-proportional ($v_i(\mathcal S_i) \ge b_i$ for both agents), there are prices $p$ such that $(\mathcal S, p)$ is a competitive equilibrium;
--   2. if $\mathcal S$ is anti-proportional ($v_i(\mathcal S_i) \le b_i$ for both agents, strictly for at least one), there are prices $p$ such that $(\mathcal S, p)$ is a competitive equilibrium.
--
--   $$\mathcal S \text{ PO and (budget-proportional or anti-proportional)} \;\Longrightarrow\; \exists\, p:\ (\mathcal S, p) \text{ is a CE}.$$
--
--   This is the easy case of CE existence: whenever an allocation exists that gives everyone her budget share, a CE exists. It is the first step of the proof of Lemma 8.2.
--
--   **Formalization Note** Agents are indexed $0, 1$ for the paper's $1, 2$. The proportional share is written $b_i\,v_i(M)$, equal to $b_i$ under normalization. Valuations are strict without the paper's identical-items exception. The statement is identical, up to its namespace, to the Proposition 5.1 milestone of mission 1 of this series.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 12, Proposition 5.1

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

namespace GenericBudgets.IdenticalPrefs

theorem proposition_5_1 {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, GenericBudgets.AlmostEqual.IsStandardValuation (v i))
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1)
    (σ : Fin m → Fin 2) (hPO : GenericBudgets.AlmostEqual.IsPO v σ) :
    (GenericBudgets.AlmostEqual.IsBudgetProportional v b σ → ∃ p, GenericBudgets.AlmostEqual.IsCE v b σ p) ∧
      (GenericBudgets.AlmostEqual.IsAntiProportional v b σ → ∃ p, GenericBudgets.AlmostEqual.IsCE v b σ p) := by sorry
end GenericBudgets.IdenticalPrefs
