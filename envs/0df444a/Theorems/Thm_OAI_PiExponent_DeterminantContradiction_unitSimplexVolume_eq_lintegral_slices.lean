-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_eq_lintegral_slices
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_eq_lintegral_slices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:03:05.864661+00:00
-- url     : https://prove2.me/theorems/3700e464-0722-4ef6-b4c7-0a22ee6ca523
-- title:
--   Unit simplex volume as an integral over slices
-- statement:
--   Slice the simplex by its last coordinate. The coordinate constraints restrict that coordinate to `[0,1]`, and the remaining coordinates form the simplex with cutoff `1 - t`; integrating the fiber volumes gives the original volume.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_eq_lintegral_slices (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      ∫⁻ t : Real,
        (if t ∈ Set.Icc (0 : Real) 1 then
          MeasureTheory.volume
            {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
              (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t}
        else 0) ∂MeasureTheory.volume := by sorry
