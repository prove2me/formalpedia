-- Prove2me | Theorems.Thm_GreedyRegionGrowing_Layouts_Supplement_lemma_3_3
-- name    : GreedyRegionGrowing.Layouts.Supplement.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:28:27.760974+00:00
-- url     : https://prove2.me/theorems/239aeaec-d15c-4c54-a4a1-cefc48ef5abb
-- title:
--   Lemma 3.3 — Region growing
-- statement:
--   Let V be a positive nondecreasing piecewise affine volume function with finite event set and nonnegative derivative c outside the events. For 0<a<b there exists a radius r strictly between a and b, outside the event set, satisfying the following inequality.
--
--   $$
--   c(r)\le\frac{k}{b-a}V(r),\qquad k=\left\lceil\log_2\frac{2V(b)}{V(a)}\right\rceil.
--   $$
--
--   This is a supporting result for Theorem 1.5.
--
--   Differences from the source:
--   - encoding: positive nondecreasing piecewise affine volume with finitely many events and nonnegative derivative away from them → the four volume axioms stated directly on positive real radii, without a global upper bound or normalization parameter; reason: Lemma 3.3 does not assume a normalization; the published VolumeFunction predicate also bundles a bound needed for deficits, which would exclude valid unbounded volumes such as V(r)=r
-- source:
--   Aditya Anand, Greedy Region Growing: Improved Approximations for Cutwidth, Pathwidth, Flow-Expander Decomposition, and More, STOC 2027 submission #506 (October 2026). Citation basis: published (canonical held submission); 46 pages; printed page = PDF page throughout (offset 0); no arXiv version. Lemma 3.3, p. 18 (PDF p. 18).

import Mathlib
import Definitions.Def_GreedyRegionGrowing_Layouts_Foundation

noncomputable section
open Finset QAlgorithms.Complexity

namespace GreedyRegionGrowing.Layouts.Supplement
attribute [local instance] Classical.propDecidable

/-- Aditya Anand, STOC 2027 submission #506 (October 2026), lemma 3 3. -/
theorem lemma_3_3 (V c : ℝ → ℝ) (E : Finset ℝ) (a b : ℝ)
    (hV : (∀ r, 0 < r → 0 < V r) ∧
      MonotoneOn V (Set.Ioi 0) ∧
      (∀ x y, 0 < x → x < y → (∀ e ∈ E, e ∉ Set.Ioo x y) →
        ∃ m q : ℝ, ∀ r ∈ Set.Ioo x y, V r = m*r+q) ∧
      (∀ r, 0 < r → r ∉ E → 0 ≤ c r ∧ HasDerivAt V (c r) r))
    (ha : 0 < a) (hab : a < b) :
  ∃ r ∈ Set.Ioo a b, r ∉ E ∧
    c r ≤ (Int.ceil (Real.logb 2 (2*V b/V a)) : ℝ)/(b-a)*V r := by sorry

end GreedyRegionGrowing.Layouts.Supplement
