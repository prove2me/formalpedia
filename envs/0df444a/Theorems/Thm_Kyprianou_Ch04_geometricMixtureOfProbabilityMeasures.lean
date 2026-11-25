-- Prove2me | Theorems.Thm_Kyprianou_Ch04_geometricMixtureOfProbabilityMeasures
-- name    : Kyprianou.Ch04.geometricMixtureOfProbabilityMeasures
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:08:19.283007+00:00
-- url     : https://prove2.me/theorems/9e460018-005a-443e-8ff3-06bcbadfb356
-- title:
--   Geometric mixture of probability measures has unit total mass
-- statement:
--   For 0≤rho<1, if every input law nu_n is a probability measure, then the sum of measures weighted by (1-rho)rho^n is again a probability measure. This is the probabilistic normalisation component of the Pollaczek–Khinchine geometric convolution expansion in Kyprianou Theorem 4.10.
-- source:
--   Kyprianou (2006), Theorem 4.10, p. 100, geometric convolution measure normalisation; abstract probability-measure lemma.

import Mathlib
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Measure.MeasureSpace
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.geometricMixtureOfProbabilityMeasures
    {α : Type*} [MeasurableSpace α]
    (rho : ENNReal) (hRho : rho < 1)
    (nu : ℕ → Measure α) (hNu : ∀ n, IsProbabilityMeasure (nu n)) :
    IsProbabilityMeasure
      (Measure.sum (fun n : ℕ => ((1 - rho) * rho ^ n) • nu n)) := by
  sorry
