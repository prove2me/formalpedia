-- Prove2me | Theorems.Thm_OAI_Problem356_isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
-- name    : OAI.Problem356.isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:40:00.468996+00:00
-- url     : https://prove2.me/theorems/5d57fb68-f6b7-4b30-995f-d86528be684f
-- title:
--   Normalized form of the smooth density construction
-- statement:
--   Let $a_i\ge0$ with $\sum_ia_i=1$, and let $g_i\ge0$ be smooth, compactly supported, with pairwise disjoint supports and
--   $$
--   \int_{\mathbb{R}^3}g_i^2=1 .
--   $$
--   Then $\sum_ia_ig_i^2$ is a smooth compact probability density.
--
--   The component weights $\frac13,\frac16,\dots,\frac16$ and unit-mass squared amplitudes fit this form.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/DisjointSquares.lean#L85-L113

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
universe uIndex uX
open MeasureTheory
open scoped BigOperators

theorem OAI.Problem356.isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
    {ι : Type uIndex} (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hgint : ∀ i ∈ s, (∫ x : E3, (g i x) ^ 2 ∂(volume : Measure E3)) = 1)
    (haint : (∑ i ∈ s, a i) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by sorry
