-- Prove2me | Theorems.Thm_OAI_Problem356_densityMeasure_sum_weighted_squares
-- name    : OAI.Problem356.densityMeasure_sum_weighted_squares
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:41:02.424089+00:00
-- url     : https://prove2.me/theorems/affed036-b6bf-434b-8e60-b705637f3a55
-- title:
--   A density of weighted squares is the corresponding mixture
-- statement:
--   Let $a_i\ge0$ and measurable $g_i$ on $\mathbb{R}^3$ ($i$ in a finite set). Then the density measure of $\sum_ia_ig_i^2$ satisfies
--   $$
--   \Bigl(\sum_ia_ig_i^2\Bigr)dx=\sum_ia_i\,\bigl(g_i^2\,dx\bigr) .
--   $$
--
--   No disjointness is needed. The counterexample measure is thus a mixture of its component measures with the prescribed weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/DisjointSquares.lean#L115-L136

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
universe uIndex uX
open MeasureTheory
open scoped BigOperators

theorem OAI.Problem356.densityMeasure_sum_weighted_squares {ι : Type uIndex}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hgm : ∀ i ∈ s, Measurable (g i)) :
    densityMeasure (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) • densityMeasure (fun x => (g i x) ^ 2) := by sorry
