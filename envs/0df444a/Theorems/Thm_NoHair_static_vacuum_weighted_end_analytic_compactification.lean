-- Prove2me | Theorems.Thm_NoHair_static_vacuum_weighted_end_analytic_compactification
-- name    : NoHair.static_vacuum_weighted_end_analytic_compactification
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T12:46:47.907266+00:00
-- url     : https://prove2.me/theorems/264f8396-a872-4b4e-bdb7-2e1bd51b2960
-- title:
--   Analytic compactification of a weakly asymptotically flat static vacuum end of positive mass
-- statement:
--   For a smooth static vacuum end with positive monopole, weighted H³ falloff at weight −1/2 suffices to find common analytic coordinates for the compactified metric ((1−N)/2)⁴ h and the squared lapse ratio. This is the exterior elliptic regularity assertion in the Kennefick–Ó Murchadha, Beig–Simon and Friedrich formulations. No horizon or prescribed radial gauge is assumed.
-- source:
--   D. Kennefick and N. Ó Murchadha, Weakly decaying asymptotically flat static and stationary solutions to the Einstein equations, §III, Definition 2 and (3.4), https://arxiv.org/abs/gr-qc/9311012. R. Beig and W. Simon, https://doi.org/10.1007/BF01941970. H. Friedrich, Conformal classes of asymptotically flat, static vacuum data, (1.4)–(1.6) and (2.1)–(2.6), https://doi.org/10.1088/0264-9381/25/6/065012. The weighted norm estimates and the normalized Einstein–scalar equations are verified on Prove2Me. [Weighted norm estimates](https://prove2.me/theorems/09b32f1b-ecac-4175-8a32-8d29f3123fde) · [Normalized equations](https://prove2.me/theorems/b84da6eb-e56a-4d8e-9545-dbf20e1eabbc).

import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff
open MeasureTheory

theorem NoHair.static_vacuum_weighted_end_analytic_compactification (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (R μ : ℝ) (hR : 0 < R) (hm : 0 < μ)
    (inside : ∀ x : ADMPoint, R < ‖x‖ → x∈Ω) (mono : HasStaticLapseMonopole N μ)
    (positive : ∀ x : ADMPoint, R < ‖x‖ → 0 < N x ∧ N x < 1 ∧ (h x).PosDef)
    (smooth : ∀ x : ADMPoint, R < ‖x‖ → ContDiffAt ℝ ∞ N x ∧ ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (weighted : ∀ k : ℕ, k ≤ 3 → ∀ i j : Fin 3, IntegrableOn
      (fun x : ADMPoint => ((1+‖x‖^2)^k/(1+‖x‖^2))*
        ‖iteratedFDeriv ℝ k (fun z => h z i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j) x‖^2)
      {x : ADMPoint | R < ‖x‖})
    (equations : ∀ x : ADMPoint, R < ‖x‖ →
      (∀ i j : Fin 3, staticSpatialHessian N h i j x = N x * spatialRicciTensor h x i j) ∧
      (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian N h i j x) = 0) :
    ∃ (a : StaticMinusPointChart Ω N h) (b : ADMPoint → ℝ), b 0 = 0 ∧
      AnalyticOnNhd ℝ b (ball 0 a.radius) ∧ (∀ i j, AnalyticOnNhd ℝ (fun y => a.coeff y i j) (ball 0 a.radius)) ∧
      (∀ y ∈ ball 0 a.radius, b y < 1) ∧ ∀ y ∈ a.change.source,
        0 < N (a.change y) ∧ b y = ((1-N (a.change y))/(1+N (a.change y)))^2 := by
  sorry
