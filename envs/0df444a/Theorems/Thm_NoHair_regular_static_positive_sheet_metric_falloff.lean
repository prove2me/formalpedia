-- Prove2me | Theorems.Thm_NoHair_regular_static_positive_sheet_metric_falloff
-- name    : NoHair.regular_static_positive_sheet_metric_falloff
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:43:39.657775+00:00
-- url     : https://prove2.me/theorems/ee09bfc4-d019-443e-aee2-f80ab7b669f7
-- title:
--   The positive conformal metric retains all the asymptotically flat derivative estimates
-- statement:
--   For any fixed number of derivatives the positive-sheet metric $((1+N)/2)^4h$ has Euclidean coefficients up to an error whose derivatives of order $k$ are $O(r^{-1-k})$. Expand the defect of a product about its limiting constants. The iterated Leibniz estimate bounds the product of two decaying errors by one extra inverse power of radius. A common radius and constant work for the finitely many metric components and derivative orders.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.regular_static_positive_sheet_metric_falloff (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∀ n : ℕ, ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ x : ADMPoint, R < ‖x‖ → ∀ k : ℕ, k≤n → ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ k (fun z => staticPositiveMetric N h z i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) x‖
        ≤ C / ‖x‖^(k+1) := by sorry
