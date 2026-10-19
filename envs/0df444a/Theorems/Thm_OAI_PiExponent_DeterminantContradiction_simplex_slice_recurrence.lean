-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_recurrence
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_slice_recurrence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T03:22:21.81462+00:00
-- url     : https://prove2.me/theorems/b5aff903-39cb-46fb-96f4-1424fa39cdf0
-- title:
--   Simplex volume by slicing
-- statement:
--   For every natural m and nonnegative r, the volume of the (m+1)-dimensional nonnegative simplex equals the integral of its m-dimensional coordinate-slice volumes. Prove this independently by a measure-preserving coordinate split and Fubini for the integrable simplex indicator; containment in [0,r]^(m+1) supplies finiteness. The cases m=0 and r=0 are included. This removes the geometric integration step from the parent, leaving dimension induction and a power integral.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_slice_recurrence (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (MeasureTheory.volume
      {x : Fin (m + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ r}).toReal =
      ∫ t in (0 : ℝ)..r,
        (MeasureTheory.volume
          {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ r - t}).toReal := by sorry
