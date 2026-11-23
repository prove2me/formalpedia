-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkedOffDiagonalEventMass
-- name    : Kyprianou.Ch01.compoundPoissonFirstMarkedOffDiagonalEventMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:54:30.951271+00:00
-- url     : https://prove2.me/theorems/52e345d1-ed68-4eba-b4f5-fbf0864d879e
-- title:
--   Independent first exponential arrival and marked offspring atom
-- statement:
--   For y,k and nonnegative t, compute the probability that the first Poisson arrival precedes y*t and its independent first mark changes population y to k. Use the independent interarrival and mark components of IsCompoundPoissonDriver, exponential arrival CDF, and the jumpLaw singleton mass p_(k+1-y). A forbidden offspring index gives zero.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4, compound-Poisson first arrival and independently marked offspring

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonFirstMarkedOffDiagonalEventMass
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ (y k : ℕ), ∀ (t : ℝ), 0 ≤ t →
      (if y ≤ k + 1 then (Q {ω | marks 0 ω = ((k + 1 - y : ℕ) : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (Real.toNNReal t : ℝ)}).toReal else 0) =
        (if y ≤ k + 1 then (offspring (k + 1 - y)).toReal else 0) *
          (1 - Real.exp (-(((rate : ℝ) * (y : ℝ)) *
            (Real.toNNReal t : ℝ)))) := by
  sorry
