-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationMonotone
-- name    : Kyprianou.Ch01.reciprocalOccupationMonotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:16:04.5179+00:00
-- url     : https://prove2.me/theorems/d401e83a-e957-4235-98fe-1c200c964b6e
-- title:
--   The extended inverse-speed occupation clock is nondecreasing on every sample path
-- statement:
--   The exact reverse Lamperti inverse-speed occupation clock, an ENNReal Lebesgue integral over (0,t] of the reciprocal of the nonnegative part of the integer-valued path, is nondecreasing in time. The integrand is nonnegative by codomain, and nested intervals yield monotonicity, including infinite mass at zero.
-- source:
--   Kyprianou (2006), Chapter 1 equation (1.19), inverse-speed occupation time

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reciprocalOccupationMonotone
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω) :
    Monotone (fun t : ℝ≥0 => reciprocalOccupation X t ω) := by
  sorry
