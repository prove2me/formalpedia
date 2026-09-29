-- Prove2me | Theorems.Thm_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg
-- name    : Manifold.exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/05218f77-276c-5ea5-9313-37fbd89035d4
-- title:
--   Liouville's theorem on a compact Riemann surface
-- statement:
--   Let $M$ be a topological space equipped with a charted space structure over $\mathbb{C}$ making it an analytic manifold with model $\mathcal{I}(\mathbb{C},\mathbb{C})$ (so a Riemann surface), and assume $M$ is compact and connected. Let $g : M \to \mathbb{C}$ be a function such that, for every $x \in M$, the reading of $g$ in the extended chart at $x$, namely $z \mapsto g\bigl((\mathrm{extChartAt}\ \mathcal{I}(\mathbb{C},\mathbb{C})\ x)^{-1}(z)\bigr)$, is meromorphic at the centre $\mathrm{extChartAt}\ \mathcal{I}(\mathbb{C},\mathbb{C})\ x\,(x)$, and such that its `meromorphicOrderAt` at that point is at least $0$ (no pole there, the singularity being at worst removable). The conclusion asserts the existence of a single constant $C \in \mathbb{C}$ such that, for every $x \in M$, the chart reading $z \mapsto g\bigl((\mathrm{extChartAt}\ \mathcal{I}(\mathbb{C},\mathbb{C})\ x)^{-1}(z)\bigr)$ agrees with the constant function $C$ on a punctured neighbourhood of the centre, i.e. eventually with respect to the filter $\mathcal{N}[\neq]$ at $\mathrm{extChartAt}\ \mathcal{I}(\mathbb{C},\mathbb{C})\ x\,(x)$. Nothing is asserted about the values of $g$ itself at the chart centres.
--
--   This is Liouville's theorem for compact Riemann surfaces — a function holomorphic in every chart is constant — stated in a form tolerant of removable singularities, so that both hypothesis and conclusion concern only punctured neighbourhoods of chart centres. It is used in the construction of a nonzero linear relation, with polynomial coefficients of bounded degree, among the chart readings of finitely many such functions, in [`Manifold.exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card`](thm.html#Manifold.exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology

theorem Manifold.exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (g : M → ℂ)
    (hg : ∀ x : M, MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hg0 : ∀ x : M, 0 ≤ meromorphicOrderAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x)) :
    ∃ C : ℂ, ∀ x : M, (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] fun _ => C := by sorry
