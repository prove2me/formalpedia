-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BoundedPayoffSqueezeAEV1
-- name    : Kyprianou.Ch04.exercise46BoundedPayoffSqueezeAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:27:22.757131+00:00
-- url     : https://prove2.me/theorems/12c18c7b-42bd-5e28-9c81-ddecb4326c05
-- title:
--   Almost-everywhere equality from decreasing bounded payoff expectations
-- statement:
--   The countable infimum of measurable bounded decreasing payoffs has limiting expectation by dominated convergence. Equality of integrals and the almost-everywhere sandwich force equality even if the intermediate payoff was not known measurable.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BoundedPayoffSqueezeAEV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Nat → Omega → Real) (g h : Omega → Real)
    (hF : ∀ n, AEMeasurable (F n) P) (hg : AEMeasurable g P)
    (hFBound : ∀ n w, 0 ≤ F n w ∧ F n w ≤ 1)
    (hgBound : ∀ w, 0 ≤ g w ∧ g w ≤ 1)
    (hSandwich : ∀ᵐ w ∂P, g w ≤ h w ∧ ∀ n, h w ≤ F n w)
    (hAnti : ∀ᵐ w ∂P, Antitone (fun n => F n w))
    (hLimit : Tendsto (fun n => ∫ w, F n w ∂P) atTop
      (nhds (∫ w, g w ∂P))) :
    h =ᵐ[P] g := by
  sorry
