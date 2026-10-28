-- Prove2me | Theorems.Thm_Gradient_hasDerivAt_line_gradient
-- name    : Gradient.hasDerivAt_line_gradient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T04:18:50.34478+00:00
-- url     : https://prove2.me/theorems/11e94112-89b7-47f4-890d-eea1cb62e875
-- title:
--   Derivative along a line, for Mathlib’s `gradient`
-- statement:
--   Let $H$ be a real inner product space and let $h : H \to \mathbb{R}$ be differentiable.
--   For fixed $x, v \in H$, the restriction of $h$ to the line through $x$ in direction $v$ is
--   differentiable at every $t \in \mathbb{R}$, with
--
--   $$
--   \frac{d}{dt}\, h(x + t v) \;=\; \bigl\langle \nabla h(x + t v),\, v \bigr\rangle .
--   $$
--
--   The one-dimensional restriction is what makes the mean value theorem and one-dimensional
--   integration available to an argument about a function on a space, and it is the bridge from
--   which the descent lemma is obtained. Stated here with `gradient h` as a function of the point;
--   `Gradient.hasDerivAt_line` is the same fact for an explicitly supplied gradient map.
-- source:
--   Y. Nesterov, Lectures on Convex Optimization, 2nd ed., Springer 2018, Lemma 1.2.3 and Theorem 2.1.2. Carved from the accepted proof of NesterovFB.Weak.theorem_3 (the rate of convergence of Nesterov’s accelerated forward-backward method), https://prove2.me/submissions/e3454a9c-3502-4c6b-9794-7eebefc4332c

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_NesterovFB_Weak_Algorithm

open Filter Topology NNReal
open InnerProductSpace
open ThreeOpSplitting.ConvexRates

theorem Gradient.hasDerivAt_line_gradient {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hd : Differentiable ℝ h) (x v : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => h (x + s • v)) ⟪gradient h (x + t • v), v⟫_ℝ t := by sorry
