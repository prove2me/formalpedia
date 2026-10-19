-- Prove2me | Theorems.Thm_OAI_Problem356_sqrt_sum_disjoint_squares
-- name    : OAI.Problem356.sqrt_sum_disjoint_squares
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:38:19.556875+00:00
-- url     : https://prove2.me/theorems/eee02cab-9378-453b-8ddf-9552fd43d132
-- title:
--   Square root of a sum of disjointly supported squares
-- statement:
--   Let $a_i\ge0$ and $g_i\ge0$ ($i$ in a finite set) be functions on $X$ whose supports are pairwise disjoint. Then for every $x$,
--   $$
--   \sqrt{\sum_ia_i\,g_i(x)^2}=\sum_i\sqrt{a_i}\,g_i(x) .
--   $$
--
--   The square root of the assembled density is then a finite sum of smooth functions. No nonsmooth composition with $\sqrt{\cdot}$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/DisjointSquares.lean#L14-L48

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
universe uIndex uX
open MeasureTheory
open scoped BigOperators

theorem OAI.Problem356.sqrt_sum_disjoint_squares {ι : Type uIndex} {X : Type uX} (s : Finset ι)
    (a : ι → ℝ) (g : ι → X → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (x : X) :
    Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, Real.sqrt (a i) * g i x := by sorry
