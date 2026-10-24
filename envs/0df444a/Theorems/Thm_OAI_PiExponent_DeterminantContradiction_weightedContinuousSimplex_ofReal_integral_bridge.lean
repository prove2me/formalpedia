-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_ofReal_integral_bridge
-- name    : OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_ofReal_integral_bridge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:53:44.635992+00:00
-- url     : https://prove2.me/theorems/b3fefc91-dcc2-4a15-9c22-b512d61e19cc
-- title:
--   Convert a nonnegative real integral to an ENNReal integral
-- statement:
--   For a set and a real function nonnegative almost everywhere and integrable under restricted volume, the `ENNReal` integral of `ofReal f` equals `ofReal` of the real set integral. This is the measure-theoretic bridge used by the parent. Mathlib’s `ofReal_integral_eq_lintegral_ofReal` in `Mathlib.MeasureTheory.Integral.Bochner.Basic` provides the conversion; relate its whole-space integrals to these set integrals using the restricted measure.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_ofReal_integral_bridge (s : Set Real) (f : Real → Real) (h_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict s] f) (h_integrable : MeasureTheory.Integrable f (MeasureTheory.volume.restrict s)) : (∫⁻ t in s, ENNReal.ofReal (f t) ∂MeasureTheory.volume) = ENNReal.ofReal (∫ t in s, f t ∂MeasureTheory.volume) := by sorry
