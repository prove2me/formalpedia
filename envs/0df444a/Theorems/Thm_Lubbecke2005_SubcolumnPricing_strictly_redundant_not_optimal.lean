-- Prove2me | Theorems.Thm_Lubbecke2005_SubcolumnPricing_strictly_redundant_not_optimal
-- name    : Lubbecke2005.SubcolumnPricing.strictly_redundant_not_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T15:26:31.142893+00:00
-- url     : https://prove2.me/theorems/3048f8fc-739d-4ca9-846d-539e196236b8
-- title:
--   Proposition 2 — a strictly redundant column is never optimal for the ratio pricing problem (31)
-- statement:
--   Consider a set-partitioning master problem with rows $\{1,\dots,m\}$, a finite collection $\mathcal A$ of nonempty columns (subsets of the rows, with incidence vectors $\mathbf a \in \{0,1\}^m$) and costs $\mathbf c$. Let $(\mathcal A, \mathbf c)$ satisfy the subcolumn property ($c_r < c_s$ for all $r, s \in \mathcal A$ with $r \subsetneq s$), and let $\bar{\mathbf u} \in \mathbb R^m$ be an arbitrary vector of dual multipliers. If $\mathbf a_s \in \mathcal A$ is a strictly redundant column, i.e. there are $\lambda_r \ge 0$ with
--   $$\mathbf a_s = \sum_{r \in \mathcal A,\ r \subsetneq s} \mathbf a_r \lambda_r \qquad\text{and}\qquad c_s > \sum_{r \in \mathcal A,\ r \subsetneq s} c_r \lambda_r ,$$
--   then $\mathbf a_s$ is not an optimal solution of the ratio pricing problem
--   $$\min\left\{ \frac{c(\mathbf a) - \bar{\mathbf u}^{\mathsf T}\mathbf a}{\mathbf 1^{\mathsf T}\mathbf a} \;\middle|\; \mathbf a \in \mathcal A \right\}, \tag{31}$$
--   that is, it is not the case that the ratio of $\mathbf a_s$ is at most the ratio of every column of $\mathcal A$.
--
--   The result says that pricing by reduced cost per covered row, instead of by reduced cost alone (Dantzig's rule), never selects a column whose dual constraint is strictly implied by those of its subcolumns. The paper states the proposition and attributes the concept to Sol (1994); it gives no proof.
--
--   **Formalization Note.** The paper leaves the sign of $\lambda_r$ in (30) implicit; this statement reads it as $\lambda_r \ge 0$, the Farkas form of "the corresponding constraint is redundant for the dual problem" (with signed multipliers the proposition is false). The sums range over the columns of $\mathcal A$ that are proper subsets of $s$. The hypothesis $\emptyset \notin \mathcal A$ is the reading of the denominator $\mathbf 1^{\mathsf T}\mathbf a$ in (31): a set-partitioning column covers at least one row (Lean's division by $0$ would otherwise give the empty column ratio $0$). The multipliers $\bar{\mathbf u}$ are free, as the rows are equalities; no sign or optimality is assumed. "Cannot be an optimal solution" is stated literally as $\neg(\forall \mathbf a \in \mathcal A,\ \text{ratio}(\mathbf a_s) \le \text{ratio}(\mathbf a))$, which is equivalent to the existence of a column of $\mathcal A$ with strictly smaller ratio. The subcolumn property is the paper's hypothesis and is kept, although the conclusion may not need it.
-- source:
--   Lübbecke and Desrosiers, Selected Topics in Column Generation, Operations Research 53(6), 2005, p. 1016, Proposition 2, Eq. (31); definitions p. 1015, Eq. (30)

import Mathlib
import Definitions.Def_Lubbecke2005_SubcolumnPricing_Columns

namespace Lubbecke2005.SubcolumnPricing

theorem strictly_redundant_not_optimal {m : ℕ} (𝒜 : Finset (Finset (Fin m)))
    (c : Finset (Fin m) → ℝ) (u : Fin m → ℝ)
    (h𝒜 : ∅ ∉ 𝒜) (hsub : SubcolumnProperty 𝒜 c)
    (s : Finset (Fin m)) (hs : s ∈ 𝒜) (hred : IsStrictlyRedundant 𝒜 c s) :
    ¬ (∀ a ∈ 𝒜, pricingRatio c u s ≤ pricingRatio c u a) := by sorry

end Lubbecke2005.SubcolumnPricing
