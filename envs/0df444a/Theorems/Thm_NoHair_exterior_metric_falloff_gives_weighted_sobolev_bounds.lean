-- Prove2me | Theorems.Thm_NoHair_exterior_metric_falloff_gives_weighted_sobolev_bounds
-- name    : NoHair.exterior_metric_falloff_gives_weighted_sobolev_bounds
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:46:42.943911+00:00
-- url     : https://prove2.me/theorems/09b32f1b-ecac-4175-8a32-8d29f3123fde
-- title:
--   Exterior metric falloff implies the weighted Sobolev bounds at weight −1/2
-- statement:
--   On a three-dimensional end, pointwise order-k metric falloff O(r⁻¹⁻ᵏ) makes all the defining weighted square integrals of Hˢ at weight −1/2 finite on one common tail, for every finite derivative order s.
-- source:
--   D. Kennefick and N. Ó Murchadha, Weakly decaying asymptotically flat static and stationary solutions to the Einstein equations, §III, Definition 2 and (3.4), https://arxiv.org/abs/gr-qc/9311012. R. Beig and W. Simon, https://doi.org/10.1007/BF01941970. H. Friedrich, Conformal classes of asymptotically flat, static vacuum data, (1.4)–(1.6) and (2.1)–(2.6), https://doi.org/10.1088/0264-9381/25/6/065012.

import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff
open MeasureTheory

theorem NoHair.exterior_metric_falloff_gives_weighted_sobolev_bounds (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (s : ℕ)
    (smooth : ∀ x : ADMPoint, B < ‖x‖ → ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (falloff : ∀ k : ℕ, ∃ L C : ℝ, 0 < L ∧ 0 < C ∧ ∀ x : ADMPoint, L < ‖x‖ → ∀ i j,
       ‖iteratedFDeriv ℝ k (fun z => h z i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j) x‖ ≤ C/‖x‖^(k+1)) :
    ∃ R : ℝ, max B 1 ≤ R ∧ ∀ k : ℕ, k ≤ s → ∀ i j : Fin 3, IntegrableOn
      (fun x : ADMPoint => ((1+‖x‖^2)^k/(1+‖x‖^2))*
        ‖iteratedFDeriv ℝ k (fun z => h z i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j) x‖^2)
      {x : ADMPoint | R < ‖x‖} := by
  sorry
