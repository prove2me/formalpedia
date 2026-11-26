-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedPartsHorizonMeasurable
-- name    : Kyprianou.Ch04.signedPartsHorizonMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:11:19.293106+00:00
-- url     : https://prove2.me/theorems/a5a68bc6-4baa-4055-9ac7-f2843db39d24
-- title:
--   signedPartsHorizonMeasurable
-- statement:
--   Joint past-horizon measurability is preserved by both signed parts.
-- source:
--   Kyprianou (2006), Exercise 4.3(i)-(ii), pp. 106-107.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The positive and negative parts of a signed past-horizon cutoff are jointly measurable. -/
theorem Kyprianou.Ch04.signedPartsHorizonMeasurable {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (k : ℝ → ℝ → Omega → ℝ) (t : NNReal)
    (hm : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0)) :
    Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then max (k z.2.1 z.2.2 z.1) 0 else 0) ∧
    Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then max (-k z.2.1 z.2.2 z.1) 0 else 0) := by
  sorry
