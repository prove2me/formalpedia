-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianFirstUpperPassageAlmostSureFinitePublic
-- name    : Kyprianou.Ch01.brownianFirstUpperPassageAlmostSureFinitePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:13:46.148935+00:00
-- url     : https://prove2.me/theorems/923f171a-51cb-4492-93d3-f4e2e422d35d
-- title:
--   Zero-drift Brownian upward first passage is almost surely finite
-- statement:
--   A centred Brownian path with variance coefficient 1 crosses each strictly positive upper barrier in finite time almost surely. The proved half-stable Brownian first-passage Laplace transform at q=0 has expectation one; its payoff equals 1 if the passage occurs and zero otherwise. The complement is nonnegative and integrable with expectation zero, hence vanishes almost everywhere.
-- source:
--   Kyprianou (2006) Chapter 1, Brownian ascending first-passage and Exercise 1.10(ii) at q=0.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageStableHalf
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianFirstUpperPassageAlmostSureFinitePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (s : ℝ) (hs : 0 < s) :
    ∀ᵐ ω ∂P, firstUpperPassage B s ω ≠ ⊤ := by sorry
