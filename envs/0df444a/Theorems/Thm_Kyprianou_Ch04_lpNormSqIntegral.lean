-- Prove2me | Theorems.Thm_Kyprianou_Ch04_lpNormSqIntegral
-- name    : Kyprianou.Ch04.lpNormSqIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:26:51.167326+00:00
-- url     : https://prove2.me/theorems/550e2779-9d20-581d-8bc4-c2998f0ce432
-- title:
--   Squared L2 norm equals the real second moment
-- statement:
--   For a square-integrable real function, the square of the norm of its L2 equivalence class equals the integral of the square of the function.
-- source:
--   Mathlib Lp norm definition and real power formula; used in Exercise 4.4 of Kyprianou (2006).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch04.lpNormSqIntegral
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : MemLp X 2 P) :
    ‖hX.toLp X‖ ^ 2 = ∫ ω, (X ω) ^ 2 ∂P := by
  sorry
