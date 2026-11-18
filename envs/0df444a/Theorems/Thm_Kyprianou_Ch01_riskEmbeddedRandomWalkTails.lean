-- Prove2me | Theorems.Thm_Kyprianou_Ch01_riskEmbeddedRandomWalkTails
-- name    : Kyprianou.Ch01.riskEmbeddedRandomWalkTails
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:22:30.05553+00:00
-- url     : https://prove2.me/theorems/3acd491d-e476-4b2c-98f1-c14a673f151c
-- title:
--   Exercise 1.8(iii): exponential-minus-claim embedded walk tail laws
-- statement:
--   Exercise 1.8(iii), printed p. 30: the embedded risk random walk has increments e_beta−ξ, with e_beta independent exponential of rate β=λ/c and ξ a positive claim of law F. The positive tail is P(e_beta−ξ>z)=e^(−βz)E[e^(−βξ)] for z≥0. The negative tail is P(e_beta−ξ<−z)=E[F((e_beta+z,∞))] for z>0. The draft constructs the increment law explicitly as a product-measure pushforward, preserving independence without assuming the tail formula.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.8(iii), printed p. 30.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.riskEmbeddedRandomWalkTails
    (beta : ℝ) (hbeta : 0 < beta)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hClaims : F (Set.Iic (0 : ℝ)) = 0) :
    let Ebeta : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun e : ℝ => ENNReal.ofReal
          (beta * Real.exp (-beta * e)))
    let mu : Measure ℝ :=
      (Ebeta.prod F).map
        (fun pair : ℝ × ℝ => pair.1 - pair.2)
    (∀ z : ℝ, 0 ≤ z →
      (mu (Set.Ioi z)).toReal =
        Real.exp (-beta * z) *
          (∫ u : ℝ, Real.exp (-beta * u) ∂F)) ∧
    (∀ z : ℝ, 0 < z →
      (mu (Set.Iio (-z))).toReal =
        (∫ e : ℝ, (F (Set.Ioi (e + z))).toReal ∂Ebeta)) := by
  sorry
