-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_preimage_smul
-- name    : OAI.PiExponent.DeterminantContradiction.volume_preimage_smul
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:27:24.212133+00:00
-- url     : https://prove2.me/theorems/40f015df-3482-4439-b43b-c006a638c599
-- title:
--   Volume under scalar dilation preimage
-- statement:
--   For a measurable set in `Fin m → Real`, taking the preimage under positive scalar dilation by c multiplies volume by c⁻ᵐ. Prove from the change-of-variables formula for an invertible linear map, computing the scalar map’s determinant as cᵐ and using that the finite-dimensional space has dimension m.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.volume_preimage_smul (m : Nat) (c : Real) (hc : 0 < c) (A : Set (Fin m → Real)) (hA : MeasurableSet A) :
    MeasureTheory.volume ((fun x => c • x) ⁻¹' A) =
      ENNReal.ofReal (c⁻¹ ^ m) * MeasureTheory.volume A := by sorry
