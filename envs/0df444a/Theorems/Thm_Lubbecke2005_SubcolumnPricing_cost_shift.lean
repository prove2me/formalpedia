-- Prove2me | Theorems.Thm_Lubbecke2005_SubcolumnPricing_cost_shift
-- name    : Lubbecke2005.SubcolumnPricing.cost_shift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T15:19:05.217518+00:00
-- url     : https://prove2.me/theorems/f860425c-29ec-44b1-84d1-12b208d9e3fb
-- title:
--   §5.1 — the cost shift $c_r := c_r + |r|$ makes weak subcolumn costs strict and adds $m$ to every partition's cost
-- statement:
--   Let $\mathcal A$ be a finite collection of columns (subsets of the rows $\{1,\dots,m\}$, with incidence vectors $\mathbf a_s \in \{0,1\}^m$) and $\mathbf c$ a cost vector such that $c_r \le c_s$ whenever $r, s \in \mathcal A$ and $r \subsetneq s$. Define the shifted costs $c'_s := c_s + |s|$. Then:
--
--   1. $(\mathcal A, \mathbf c')$ satisfies the subcolumn property: $c'_r < c'_s$ for all $r, s \in \mathcal A$ with $r \subsetneq s$;
--   2. for every $\lambda \in \mathbb R^{\mathcal A}$ satisfying the set-partitioning constraints $\sum_{s \in \mathcal A} \mathbf a_s \lambda_s = \mathbf 1$,
--   $$\sum_{s \in \mathcal A} c'_s \lambda_s = \sum_{s \in \mathcal A} c_s \lambda_s + m .$$
--
--   The paper states: "If only $c_r \leqslant c_s$ holds, strict inequality can be obtained by modifying the cost structure by $c_r := c_r + |r|$. This adds to $z^\star$ a constant term equal to the number of rows and does not change the problem." Part 2 is the pointwise form of the second sentence: the feasible set is unchanged and on it the objective is shifted by the constant $m$, so the optimal solutions are the same and the optimal value becomes $z^\star + m$. The shift therefore lets Proposition 2 be applied when the costs are only weakly monotone under inclusion.
--
--   **Formalization Note.** Columns are `Finset (Fin m)`; $|s|$ is `s.card`. Part 2 is stated for real multipliers (it covers the LP relaxation and the integer program alike, and uses no sign condition). The paper's "$z^\star$" is not formalized as an optimal value; the pointwise identity on the feasible set is the content of "adds to $z^\star$ a constant term … and does not change the problem".
-- source:
--   Lübbecke and Desrosiers, Selected Topics in Column Generation, Operations Research 53(6), 2005, p. 1016, §5.1 (sentences following the subcolumn property)

import Mathlib
import Definitions.Def_Lubbecke2005_SubcolumnPricing_Columns

namespace Lubbecke2005.SubcolumnPricing

theorem cost_shift {m : ℕ} (𝒜 : Finset (Finset (Fin m))) (c : Finset (Fin m) → ℝ)
    (hweak : ∀ r ∈ 𝒜, ∀ s ∈ 𝒜, r ⊂ s → c r ≤ c s) :
    SubcolumnProperty 𝒜 (fun s => c s + (s.card : ℝ)) ∧
    ∀ lam : Finset (Fin m) → ℝ,
      (∑ s ∈ 𝒜, lam s • incidence s) = (1 : Fin m → ℝ) →
      ∑ s ∈ 𝒜, (c s + (s.card : ℝ)) * lam s = ∑ s ∈ 𝒜, c s * lam s + (m : ℝ) := by sorry

end Lubbecke2005.SubcolumnPricing
