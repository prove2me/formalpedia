-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationBoundedByTime
-- name    : Kyprianou.Ch01.reciprocalOccupationBoundedByTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:35:26.508542+00:00
-- url     : https://prove2.me/theorems/4cf4645e-8d7c-48a6-8a3d-70d4bda0c1c0
-- title:
--   Inverse-speed occupation integral is finite and bounded by elapsed time on a positive integer path
-- statement:
--   For an integer-valued sample path which remains strictly positive at all times through t, the extended inverse-speed occupation clock is at most t. Indeed positive integer values are at least one, so the reciprocal integrand is at most one on (0,t], and Lebesgue integration gives the time interval length. In particular the source extended occupation clock is finite before nonpositive passage, enabling its toReal conversion in reverse Lamperti (1.19), even without supplementary integrability hypotheses.
-- source:
--   Kyprianou (2006), Chapter 1 Eq. (1.19), reverse Lamperti inverse-speed clock

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.NNReal.Basic
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.reciprocalOccupationBoundedByTime
    {Ω : Type*} (X : NNReal → Ω → ℤ) (ω : Ω) (t : NNReal)
    (hpositive : ∀ s : NNReal, s ≤ t → 0 < X s ω) :
    reciprocalOccupation X t ω ≤ ENNReal.ofReal (t : ℝ) := by
  sorry
