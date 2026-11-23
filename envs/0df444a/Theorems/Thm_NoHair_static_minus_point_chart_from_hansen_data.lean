-- Prove2me | Theorems.Thm_NoHair_static_minus_point_chart_from_hansen_data
-- name    : NoHair.static_minus_point_chart_from_hansen_data
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:28:57.034149+00:00
-- url     : https://prove2.me/theorems/a223e28c-4ff9-4393-bba4-3bff6a897fbd
-- title:
--   Transfer of a smooth Hansen compactification to the negative conformal sheet
-- statement:
--   Suppose the compactified quotient metric and the squared lapse ratio b are smooth in common coordinates at infinity. Multiplying the quotient metric by (1−b)²/16 gives exactly the Bunting–Masood-ul-Alam negative-sheet metric and produces its smooth positive point chart.
-- source:
--   R. Beig and W. Simon, Proof of a multipole conjecture due to Geroch, Comm. Math. Phys. 78 (1980), 75–82, https://doi.org/10.1007/BF01941970. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. These statements concern the lapse and its radial coordinate near the compactified end.

import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff

theorem NoHair.static_minus_point_chart_from_hansen_data (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ∃ (a : StaticMinusPointChart Ω N (fun x : ADMPoint => (((1+N x)^4)/(N x)^2) • h x)) (b : ADMPoint → ℝ),
      b 0 = 0 ∧ ContDiffOn ℝ ∞ b (ball 0 a.radius) ∧ (∀ y ∈ ball 0 a.radius, b y < 1) ∧
      ∀ y ∈ a.change.source, 0 < N (a.change y) ∧
        b y = ((1-N (a.change y))/(1+N (a.change y)))^2) :
    Nonempty (StaticMinusPointChart Ω N h) := by
  sorry
