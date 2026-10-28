-- Prove2me | Theorems.Thm_Gradient_descent_lemma_gradient
-- name    : Gradient.descent_lemma_gradient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T04:18:36.69999+00:00
-- url     : https://prove2.me/theorems/e1743994-61b3-4c77-8f38-7faa1c5ef312
-- title:
--   The descent lemma, for Mathlib’s `gradient`
-- statement:
--   Let $H$ be a real inner product space and let $h : H \to \mathbb{R}$ be differentiable
--   with $L$-Lipschitz gradient, $\|\nabla h(x) - \nabla h(y)\| \le L\|x-y\|$ for all $x, y$ and
--   some $L \ge 0$. Then
--
--   $$
--   h(y) \;\le\; h(x) \;+\; \langle \nabla h(x),\, y - x \rangle \;+\; \frac{L}{2}\,\|y - x\|^{2}
--   \qquad \text{for all } x, y \in H .
--   $$
--
--   No convexity is required. This quadratic upper bound is the inequality on which the analysis of
--   every first-order method rests, and it is stated here in the `gradient h` phrasing;
--   `Gradient.descent_lemma` is the same fact for an explicitly supplied gradient map. Three
--   missions in this collection -- Nesterov's accelerated forward-backward method, a three-operator
--   splitting scheme, and a nonmonotone spectral projected gradient method -- each proved it
--   inline.
-- source:
--   Y. Nesterov, Lectures on Convex Optimization, 2nd ed., Springer 2018, Lemma 1.2.3 and Theorem 2.1.2. Carved from the accepted proof of NesterovFB.Weak.theorem_3 (the rate of convergence of Nesterov’s accelerated forward-backward method), https://prove2.me/submissions/e3454a9c-3502-4c6b-9794-7eebefc4332c

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_NesterovFB_Weak_Algorithm

open Filter Topology NNReal
open InnerProductSpace
open ThreeOpSplitting.ConvexRates

theorem Gradient.descent_lemma_gradient {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hd : Differentiable ℝ h) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x y : H, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖) (x y : H) :
    h y ≤ h x + ⟪gradient h x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by sorry
