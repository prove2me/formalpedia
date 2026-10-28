-- Prove2me | Theorems.Thm_Gradient_convex_first_order_gradient
-- name    : Gradient.convex_first_order_gradient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T04:18:37.12648+00:00
-- url     : https://prove2.me/theorems/1fc4c941-515b-4058-9e56-e5011656292c
-- title:
--   First-order characterization of convexity, for Mathlib’s `gradient`
-- statement:
--   Let $H$ be a real inner product space and let $h : H \to \mathbb{R}$ be differentiable
--   and convex. Then for all $x, y \in H$
--
--   $$
--   h(x) \;+\; \langle \nabla h(x),\, y - x \rangle \;\le\; h(y),
--   $$
--
--   where $\nabla h$ is the gradient.
--
--   This is the first-order convexity inequality in the phrasing that takes the gradient as a
--   *function* of the point, `gradient h`, rather than as a vector supplied with a differentiability
--   hypothesis at each point. The platform already carries the same fact in the latter phrasing as
--   `Gradient.convex_first_order`, stated for a map `G` with `HasGradientAt F (G x) x`; which of the
--   two is convenient depends on how the ambient development states differentiability, and three
--   separate missions needed this one.
--
--   **Formalization Note** Differentiability is `Differentiable ℝ h`, convexity is
--   `ConvexOn ℝ Set.univ h`, and the gradient is Mathlib's `gradient`.
-- source:
--   Y. Nesterov, Lectures on Convex Optimization, 2nd ed., Springer 2018, Lemma 1.2.3 and Theorem 2.1.2. Carved from the accepted proof of NesterovFB.Weak.theorem_3 (the rate of convergence of Nesterov’s accelerated forward-backward method), https://prove2.me/submissions/e3454a9c-3502-4c6b-9794-7eebefc4332c

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_NesterovFB_Weak_Algorithm

open Filter Topology NNReal
open InnerProductSpace
open ThreeOpSplitting.ConvexRates

theorem Gradient.convex_first_order_gradient {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hc : ConvexOn ℝ Set.univ h) (hd : Differentiable ℝ h) (x y : H) :
    h x + ⟪gradient h x, y - x⟫_ℝ ≤ h y := by sorry
