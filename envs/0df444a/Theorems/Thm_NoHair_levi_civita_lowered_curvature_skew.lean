-- Prove2me | Theorems.Thm_NoHair_levi_civita_lowered_curvature_skew
-- name    : NoHair.levi_civita_lowered_curvature_skew
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T11:46:43.022146+00:00
-- url     : https://prove2.me/theorems/241014b1-c1de-4268-ab72-3afdef921cfd
-- title:
--   Metric compatibility makes spatial curvature skew in its lowered indices
-- statement:
--   Differentiate metric compatibility in both coordinate orders. Equality of mixed derivatives cancels the second derivatives of the metric. The remaining Christoffel terms give skew symmetry in the two lowered vector indices.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_spatialRiemannCurvature

open NoHair Set Filter Bundle
open scoped Topology ContDiff Manifold

theorem NoHair.levi_civita_lowered_curvature_skew (W : Set ADMPoint) (op : IsOpen W) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (smooth : ∀ a b, ContDiffOn ℝ ∞ (fun y => h y a b) W)
    (pos : ∀ y∈W, (h y).PosDef) (x : ADMPoint) (hx : x∈W) :
    ∀ a b i j : Fin 3, (∑ k : Fin 3, h x a k * spatialRiemannCurvature h x k b i j) =
      -(∑ k : Fin 3, h x b k * spatialRiemannCurvature h x k a i j) := by sorry
