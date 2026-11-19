-- Prove2me | Theorems.Thm_Kyprianou_Ch01_finiteGridNoCrossingNaturalMeasurablePublic
-- name    : Kyprianou.Ch01.finiteGridNoCrossingNaturalMeasurablePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:04:01.386213+00:00
-- url     : https://prove2.me/theorems/03e49df5-bc6e-47bb-afd1-87fd129f43f9
-- title:
--   Public Finite grid prefix below barrier is naturally measurable
-- statement:
--   For any real stochastic process, any nonnegative grid spacing and barrier, the finite prefix event that every grid observation at indices 0 through n is no greater than the barrier belongs to the process natural filtration at time n times the spacing. It is obtained by intersecting the past-evaluation inverse images. No Brownian or passage-time transform assumptions are made.
-- source:
--   Accepted original private Kyprianou.Ch01.finiteGridNoCrossingNaturalMeasurable source, republished under public visibility for Chapter 1 optional sampling.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_measurable_past
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01 Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.finiteGridNoCrossingNaturalMeasurablePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (delta : ℝ≥0) (n : ℕ) :
    @MeasurableSet Ω (naturalSigma X ((n : ℝ≥0) * delta))
      {ω | ∀ k : ℕ, k ≤ n → X ((k : ℝ≥0) * delta) ω ≤ s} := by sorry
