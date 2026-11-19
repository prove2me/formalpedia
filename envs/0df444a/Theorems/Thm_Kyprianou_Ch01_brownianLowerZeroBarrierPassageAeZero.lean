-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianLowerZeroBarrierPassageAeZero
-- name    : Kyprianou.Ch01.brownianLowerZeroBarrierPassageAeZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:04:50.675205+00:00
-- url     : https://prove2.me/theorems/23a9f0d2-0330-4fba-be80-f4f9a4db1234
-- title:
--   Nondegenerate Brownian motion strictly downcrosses its initial zero level immediately almost surely
-- statement:
--   For a continuous nondegenerate Brownian Lévy process started at zero and with arbitrary deterministic drift, the original first strictly positive-time downcrossing of the zero starting barrier has infimum zero almost surely (WithTop 0), preserving the original firstLowerPassage definition. This isolates the Brownian zero-regularity property needed for Exercise 1.10(ii).
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), Brownian zero-barrier regularity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianLowerZeroBarrierPassageAeZero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (sigma gamma : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    ∀ᵐ ω ∂P, firstLowerPassage X 0 0 ω = 0 := by
  sorry
