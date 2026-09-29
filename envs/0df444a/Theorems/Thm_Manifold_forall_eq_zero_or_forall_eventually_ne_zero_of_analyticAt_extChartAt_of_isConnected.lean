-- Prove2me | Theorems.Thm_Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected
-- name    : Manifold.forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/84b02d79-3ce6-5759-9b91-e0f8920aae04
-- title:
--   Identity principle for chartwise analytic functions on a connected set
-- statement:
--   Let $M$ be a topological space equipped with a charted-space structure over $\mathbb{C}$, making it a real-analytic ($\omega$) manifold modelled on $\mathbb{C}$ with the identity model-with-corners $\mathcal{I}(\mathbb{C},\mathbb{C})$, and assume $M$ is Hausdorff. Let $W \subseteq M$ be open and let $W$ be connected, i.e. nonempty and preconnected. Let $g : M \to \mathbb{C}$ be a function such that for every $x \in W$ the function $z \mapsto g\bigl((\mathrm{extChartAt}\ \mathcal{I}(\mathbb{C},\mathbb{C})\ x)^{-1}(z)\bigr)$, read in the extended chart centred at $x$, is analytic over $\mathbb{C}$ at the point $\mathrm{extChartAt}\ \mathcal{I}(\mathbb{C},\mathbb{C})\ x\ (x)$. Then one of the following holds: either $g(x) = 0$ for every $x \in W$, or for every $x \in W$ one has $g(y) \neq 0$ for all $y$ in some punctured neighbourhood of $x$, i.e. eventually with respect to the filter $\mathcal{N}[\neq] x$ of deleted neighbourhoods. Note that the first alternative asserts only pointwise vanishing on $W$, not vanishing on a neighbourhood of $W$, and that the second alternative is asserted at every point of $W$, including points outside $W$ in the punctured neighbourhoods.
--
--   This is the identity principle (isolated-zeros theorem) for a function on a one-dimensional complex manifold that is analytic when read in the extended chart at each point of a connected set: such a function either vanishes on the set or has only isolated zeros there. It is used in the treatment of places on algebraic curves, via [`AlgebraicCurve.Place.forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated`](thm.html#AlgebraicCurve.Place.forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated), where it yields finiteness of zero sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold ContDiff Topology

theorem Manifold.forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M] [T2Space M]
    {W : Set M} (hW : IsOpen W) (hWc : IsConnected W) (g : M → ℂ)
    (hg : ∀ x ∈ W, AnalyticAt ℂ (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x)) :
    (∀ x ∈ W, g x = 0) ∨ (∀ x ∈ W, ∀ᶠ y in 𝓝[≠] x, g y ≠ 0) := by sorry
