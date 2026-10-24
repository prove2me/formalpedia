-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_preimage_volume
-- name    : OAI.PiExponent.DeterminantContradiction.diagonal_preimage_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:13:59.105713+00:00
-- url     : https://prove2.me/theorems/29afa006-c26e-4e5f-a039-7f111f4dbaac
-- title:
--   Volume under positive diagonal rescaling
-- statement:
--   The preimage of a measurable set under a positive diagonal linear map scales its volume by the product of reciprocal coordinate scales. This follows from the linear change-of-variables formula and the diagonal determinant.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.diagonal_preimage_volume
    (n : Nat) (c : Fin n → Real) (hc : ∀ i, 0 < c i)
    (s : Set (Fin n → Real)) (hs : MeasurableSet s) :
    MeasureTheory.volume {x : Fin n → Real | (fun i => c i * x i) ∈ s} =
      (∏ i, ENNReal.ofReal (1 / c i)) * MeasureTheory.volume s := by sorry
