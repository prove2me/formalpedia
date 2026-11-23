-- Prove2me | Theorems.Thm_NoHair_static_quotient_einstein_scalar_equations
-- name    : NoHair.static_quotient_einstein_scalar_equations
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:52:58.295243+00:00
-- url     : https://prove2.me/theorems/b84da6eb-e56a-4d8e-9545-dbf20e1eabbc
-- title:
--   The normalized static quotient satisfies the three-dimensional Einstein–scalar equations
-- statement:
--   On every region of positive static lapse, the quotient metric γ=N²h and potential u=log N satisfy Ric(γ)=2 du⊗du and Δγu=0. Harmonicity is expressed as the vanishing divergence of the γ-metric gradient density. These are the equations used to bootstrap regularity at infinity in harmonic coordinates.
-- source:
--   D. Kennefick and N. Ó Murchadha, Weakly decaying asymptotically flat static and stationary solutions to the Einstein equations, §III, Definition 2 and (3.4), https://arxiv.org/abs/gr-qc/9311012. R. Beig and W. Simon, https://doi.org/10.1007/BF01941970. H. Friedrich, Conformal classes of asymptotically flat, static vacuum data, (1.4)–(1.6) and (2.1)–(2.6), https://doi.org/10.1088/0264-9381/25/6/065012.

import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff
open MeasureTheory

theorem NoHair.static_quotient_einstein_scalar_equations (W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hW : IsOpen W) (sn : ContDiffOn ℝ ∞ N W) (sh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W)
    (positive : ∀ x ∈ W, 0 < N x ∧ (h x).PosDef)
    (equations : ∀ x ∈ W,
      (∀ i j : Fin 3, staticSpatialHessian N h i j x = N x * spatialRicciTensor h x i j) ∧
      (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian N h i j x) = 0) :
    let γ : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := fun y => N y^2 • h y
    let u := fun y => Real.log (N y)
    ∀ x ∈ W, (∀ i j : Fin 3, spatialRicciTensor γ x i j = 2*spatialADMPartial i u x*spatialADMPartial j u x) ∧
      (∑ i : Fin 3, spatialADMPartial i (fun y => Real.sqrt (γ y).det * staticRaisedGradient u γ i y) x) = 0 := by
  sorry
