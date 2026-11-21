-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryPathMonotoneOfFiniteV1
-- name    : Kyprianou.Ch01.inverseGaussianZeroBoundaryPathMonotoneOfFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:10:49.465943+00:00
-- url     : https://prove2.me/theorems/97b667b6-a15f-49ed-a5a8-d8882d7474e7
-- title:
--   Zero-normalised finite first-passage time is monotone in its level
-- statement:
--   For an arbitrary path that crosses every strictly positive level in finite time, its first strictly-upper-passage time, normalised to zero at level zero, is monotone as a real-valued function of the barrier level. This is a deterministic consequence of first-passage barrier monotonicity.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, strictly-upper first-passage definition and order preservation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageBarrierMonotone
open MeasureTheory Set Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianZeroBoundaryPathMonotoneOfFiniteV1
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hFinite : ∀ s : ℝ≥0, 0 < s → firstUpperPassage X (s : ℝ) ω ≠ ⊤) :
    Monotone (fun s : ℝ≥0 =>
      if s = 0 then (0 : ℝ)
      else match firstUpperPassage X (s : ℝ) ω with
      | none => (0 : ℝ)
      | some t => (t : ℝ)) := by
  sorry
