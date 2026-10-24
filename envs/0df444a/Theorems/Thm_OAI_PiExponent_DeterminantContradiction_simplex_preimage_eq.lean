-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_preimage_eq
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_preimage_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:26:45.704827+00:00
-- url     : https://prove2.me/theorems/f660b2b2-cc0f-48c5-a4fd-b68571663a57
-- title:
--   Simplex as a dilation preimage
-- statement:
--   For positive s and T, the size-s simplex is exactly the preimage of the size-T simplex under dilation by T/s. Prove by extensionality, using positivity to preserve coordinate inequalities and the sum inequality under multiplication.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_preimage_eq (m : Nat) (s T : Real) (hs : 0 < s) (hT : 0 < T) :
    {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < s} =
      (fun x => (T / s) • x) ⁻¹' {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} := by sorry
