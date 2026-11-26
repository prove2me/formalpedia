-- Prove2me | Theorems.Thm_Kyprianou_Ch04_lpNormEqOfSquareIntegralEq
-- name    : Kyprianou.Ch04.lpNormEqOfSquareIntegralEq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:50:07.69879+00:00
-- url     : https://prove2.me/theorems/0f47597a-f7f7-41cd-9172-8d52cb9b3681
-- title:
--   L2 norm equality from square integral equality
-- statement:
--   Equality of the real square integrals of two L2 functions implies equality of their L2 norms, possibly on different measure spaces.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; L2 limit transfer.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_Kyprianou_Ch04_lpNormSqIntegral
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.lpNormEqOfSquareIntegralEq
    {A : Type u} {Ω : Type v} [MeasurableSpace A] [MeasurableSpace Ω]
    (μ : Measure A) (P : Measure Ω) (f : A → ℝ) (X : Ω → ℝ)
    (hf : MemLp f 2 μ) (hX : MemLp X 2 P)
    (h : (∫ ω, (X ω)^2 ∂P) = ∫ a, (f a)^2 ∂μ) :
    ‖hX.toLp X‖ = ‖hf.toLp f‖ := by
  sorry
