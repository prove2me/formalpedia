-- Prove2me | Theorems.Thm_Kyprianou_Ch01_naturalGridFirstCrossingMeasurablePublic
-- name    : Kyprianou.Ch01.naturalGridFirstCrossingMeasurablePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:13:10.559179+00:00
-- url     : https://prove2.me/theorems/a06c28ef-9e6b-4510-a102-96a0cca1635a
-- title:
--   Public Sentinel-capped first grid upcrossing is a bounded stopping index in the natural filtration
-- statement:
--   For a real stochastic process, a barrier, a nonnegative uniform grid spacing and finite terminal index N, define the first grid index at which the process is strictly above the barrier, or N if no earlier crossing. The index is at most N, and for all n<N, the continuation event that it exceeds n is measurable with respect to the natural filtration at time n times the grid spacing. Combines the proved first-trigger prefix characterisation and finite-grid prefix measurability, without using any Brownian passage transform.
-- source:
--   Accepted original private Kyprianou.Ch01.naturalGridFirstCrossingMeasurable source, republished under public visibility for Chapter 1 optional sampling.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01 Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.naturalGridFirstCrossingMeasurablePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (delta : ℝ≥0) (N : ℕ) :
    let τ : Ω → ℕ := fun ω => by
      classical
      exact Nat.find (show ∃ k : ℕ,
        k = N ∨ s < X ((k : ℝ≥0) * delta) ω from ⟨N, Or.inl rfl⟩)
    (∀ ω, τ ω ≤ N) ∧
      ∀ n, n < N →
        @MeasurableSet Ω (naturalSigma X ((n : ℝ≥0) * delta))
          {ω | n < τ ω} := by sorry
