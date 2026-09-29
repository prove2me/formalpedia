-- Prove2me | Theorems.Thm_ModularForm_finiteDimensional_and_finrank_le_of_isArithmetic
-- name    : ModularForm.finiteDimensional_and_finrank_le_of_isArithmetic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/87cec281-33e2-58ad-909d-dbecf2c7d4c2
-- title:
--   Finite-dimensionality and Sturm bound for M_k(G)
-- statement:
--   Let $\mathcal{G}$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ which is arithmetic (`Subgroup.IsArithmetic`) and all of whose elements have determinant one (`Subgroup.HasDetOne`), let $k$ be an integer, and assume that $1$ belongs to $\mathcal{G}$'s set of strict periods, i.e. $1 \in \mathcal{G}.\mathrm{strictPeriods}$, so that weight-$k$ forms for $\mathcal{G}$ admit a $q$-expansion `qExpansion 1 f` in integral powers of $q = e^{2\pi i \tau}$. The assertion is a conjunction: first, the $\mathbb{C}$-vector space $\mathrm{ModularForm}\ \mathcal{G}\ k$ of weight-$k$ modular forms for $\mathcal{G}$ is finite-dimensional over $\mathbb{C}$; second, its $\mathbb{C}$-dimension satisfies
--   $$\operatorname{finrank}_{\mathbb{C}} \mathrm{ModularForm}\ \mathcal{G}\ k \;\le\; \big\lfloor (k \cdot [\,\mathcal{S}\mathcal{L} : \mathcal{G} \cap \mathcal{S}\mathcal{L}\,])^{+}/12 \big\rfloor + 1,$$
--   where $\mathcal{S}\mathcal{L}$ denotes $\mathrm{SL}_2(\mathbb{Z})$ inside $\mathrm{GL}_2(\mathbb{R})$, the index is Mathlib's relative index `𝒢.relIndex 𝒮ℒ`, the product $k \cdot [\,\mathcal{S}\mathcal{L} : \mathcal{G} \cap \mathcal{S}\mathcal{L}\,]$ is an integer truncated to a natural number by `Int.toNat`, and the division by $12$ is natural-number division. In particular, for $k < 0$ the bound degenerates to the (true but weak) inequality $\dim \le 1$.
--
--   This is the classical Sturm-bound estimate for the dimension of a space of modular forms of integral weight on an arithmetic group, packaged together with finite-dimensionality so that the numerical bound is read against a genuinely finite dimension. It is used in the comparison of mod-$p$ modular forms with characteristic-zero ones, for instance by the results bounding the cardinality of a linearly independent family of mod-$p$ forms and the cuspidal dimension formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_finiteDimensional_and_finrank_le_of_isArithmetic.lean

import Mathlib.NumberTheory.ModularForms.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.finiteDimensional_and_finrank_le_of_isArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) :
    FiniteDimensional ℂ (ModularForm 𝒢 k) ∧
      Module.finrank ℂ (ModularForm 𝒢 k) ≤ (k * 𝒢.relIndex 𝒮ℒ).toNat / 12 + 1 := by sorry
