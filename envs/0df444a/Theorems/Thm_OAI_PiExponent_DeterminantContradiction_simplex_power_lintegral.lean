-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_lintegral
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:20:28.261289+00:00
-- url     : https://prove2.me/theorems/c0319995-4c57-49cb-892e-3fccdbd96e1b
-- title:
--   Integral of the normalized simplex slice factor
-- statement:
--   Integrating the normalized m-th power of the slice size over [0,T) gives T/(m+1), including after multiplication by any fixed extended-real volume V. This removes the scalar integral evaluation from the parent. Prove by the power integral on [0,T), using nonnegative integral scaling and handling finite and infinite V. For m = 0 the integrand is constant on [0,T), so the identity gives T · V.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral (m : Nat) (T : Real) (hT : 0 < T) (V : ENNReal) :
    MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
      if 0 ≤ t ∧ t < T then
        ENNReal.ofReal (((T - t) / T) ^ m) * V
      else 0) =
      ENNReal.ofReal (T / ((m + 1 : Nat) : Real)) * V := by sorry
