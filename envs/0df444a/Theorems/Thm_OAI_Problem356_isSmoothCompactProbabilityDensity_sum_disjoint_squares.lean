-- Prove2me | Theorems.Thm_OAI_Problem356_isSmoothCompactProbabilityDensity_sum_disjoint_squares
-- name    : OAI.Problem356.isSmoothCompactProbabilityDensity_sum_disjoint_squares
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:39:06.3672+00:00
-- url     : https://prove2.me/theorems/c51961ff-cacf-40a1-94d2-cde6b717866b
-- title:
--   Smooth compact densities from disjoint smooth square roots
-- statement:
--   Let $a_i\ge0$ and let $g_i\ge0$ ($i$ in a finite set) be smooth, compactly supported functions on $\mathbb{R}^3$ with pairwise disjoint supports, such that $\int\sum_ia_ig_i^2=1$. Then
--   $$
--   \rho=\sum_ia_i\,g_i^2
--   $$
--   is a smooth compact probability density: it is nonnegative, smooth and compactly supported, its square root is smooth and compactly supported, and $\int\rho=1$.
--
--   This is how the counterexample density, which needs a smooth square root, is assembled from its five components.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/DisjointSquares.lean#L50-L83

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
universe uIndex uX
open MeasureTheory
open scoped BigOperators

theorem OAI.Problem356.isSmoothCompactProbabilityDensity_sum_disjoint_squares {ι : Type uIndex}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hmass : (∫ x : E3, (∑ i ∈ s, a i * (g i x) ^ 2)
      ∂(volume : Measure E3)) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by sorry
