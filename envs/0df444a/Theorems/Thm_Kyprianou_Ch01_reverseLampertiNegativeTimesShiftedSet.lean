-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNegativeTimesShiftedSet
-- name    : Kyprianou.Ch01.reverseLampertiNegativeTimesShiftedSet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:57:18.54258+00:00
-- url     : https://prove2.me/theorems/5dd7b9a8-3406-4fb6-bc68-4cf45fecf19b
-- title:
--   Strictly positive negative-time sets translate under nonnegative restart
-- statement:
--   For a positive constant-prefix path X coinciding after A with a shifted path Y whose time-zero value is nonnegative, the set of strictly positive physical times when X is negative equals the translation by A of the strictly positive times when Y is negative. This corrects the time-zero flaw in the original disproved reverse-Lamperti path-clock lemma. The infimum of the resulting time set supplies the first-negative-passage component of the corrected stopped-clock identity.
-- source:
--   Kyprianou (2006), Section 1.3.4, exact deterministic first-arrival negative passage set translation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNegativeTimesShiftedSet
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    {u : ℝ≥0 | 0 < u ∧ X u ω < 0} =
      (fun v : ℝ≥0 => Real.toNNReal A + v) ''
        {v : ℝ≥0 | 0 < v ∧ Y v ω < 0} := by
  sorry
