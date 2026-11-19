-- Prove2me | Theorems.Thm_Kyprianou_Ch01_uniformIntegrableOfUniformLpTwoBoundPublic
-- name    : Kyprianou.Ch01.uniformIntegrableOfUniformLpTwoBoundPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:14:20.605848+00:00
-- url     : https://prove2.me/theorems/cad06a58-88b0-4596-bc82-9ae320ffc832
-- title:
--   Uniform bounded L2 norms imply L1 uniform integrability on a probability space
-- statement:
--   For any sequence of almost-everywhere strongly measurable real random variables on a probability space, a common finite upper bound C on their L2 norms implies the sequence is uniformly integrable in L1. The proof should use Hölder on restricted measurable sets to bound the L1 norm by C times the square root of the event probability, and the probability measure's total mass to bound the L1 norms themselves. This generic result is reusable and does not require almost-sure convergence or assume any first-passage conclusion.
-- source:
--   Standard uniform-integrability criterion from an Lp bound with p greater than one; used in Kyprianou (2006) Exercise 1.10(ii).

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.uniformIntegrableOfUniformLpTwoBoundPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (f n) P)
    (C : ℝ≥0)
    (hBound : ∀ n, eLpNorm (f n) 2 P ≤ (C : ENNReal)) :
    UniformIntegrable f 1 P := by sorry
