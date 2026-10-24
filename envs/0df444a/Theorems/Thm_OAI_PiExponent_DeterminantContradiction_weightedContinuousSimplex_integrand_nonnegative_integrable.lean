-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_integrand_nonnegative_integrable
-- name    : OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_integrand_nonnegative_integrable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:06:19.35502+00:00
-- url     : https://prove2.me/theorems/561fc10c-6e19-4754-8276-06cfe654018e
-- title:
--   Simplex integrand is nonnegative and integrable
-- statement:
--   For natural `n` and positive `T`, the simplex slice integrand is almost everywhere nonnegative and integrable on `(0,T)`. Positivity follows from `T - t > 0` on the interval; continuity on the bounded interval gives integrability. This also holds when `n = 0`.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_integrand_nonnegative_integrable (n : Nat) (T : Real) (hT : 0 < T) : (0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : Real) T)] (fun t : Real => (T - t) ^ n / (n.factorial : Real))) ∧ MeasureTheory.Integrable (fun t : Real => (T - t) ^ n / (n.factorial : Real)) (MeasureTheory.volume.restrict (Set.Ioo (0 : Real) T)) := by sorry
