-- Prove2me | Theorems.Thm_NoHair_regular_static_lapse_adapted_end_chart
-- name    : NoHair.regular_static_lapse_adapted_end_chart
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T12:14:04.288797+00:00
-- url     : https://prove2.me/theorems/27a972a3-c871-4112-bc97-d4271ac79234
-- title:
--   A punctured-ball chart with the static lapse as its radial coordinate
-- statement:
--   For every regular asymptotically flat static vacuum end, the compactifying lapse ratio (1−N)/(1+N) and the original Cartesian direction are smooth coordinates on an entire neighborhood of infinity. The chart exchanges the puncture with spatial infinity and makes the rescaled squared lapse ratio exactly the Euclidean squared radius.
-- source:
--   R. Beig and W. Simon, Proof of a multipole conjecture due to Geroch, Comm. Math. Phys. 78 (1980), 75–82, https://doi.org/10.1007/BF01941970. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. These statements concern the lapse and its radial coordinate near the compactified end.

import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff

theorem NoHair.regular_static_lapse_adapted_end_chart (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ (δ : ℝ) (e : OpenPartialHomeomorph ADMPoint ADMPoint), 0 < δ ∧
      e.source = ball 0 δ ∩ ({0} : Set ADMPoint)ᶜ ∧ e.target ⊆ Ω ∧
      (∃ R : ℝ, ∀ x : ADMPoint, R < ‖x‖ → x ∈ e.target) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      Tendsto (fun y : ADMPoint => ‖e y‖) (𝓝[≠] 0) atTop ∧
      Tendsto (fun x : ADMPoint => e.symm x) (cocompact ADMPoint) (𝓝 0) ∧
      ∀ y ∈ e.source, (1-N (e y))/(1+N (e y)) = ‖y‖ ∧
        e y = (‖e y‖/‖y‖) • y := by
  sorry
