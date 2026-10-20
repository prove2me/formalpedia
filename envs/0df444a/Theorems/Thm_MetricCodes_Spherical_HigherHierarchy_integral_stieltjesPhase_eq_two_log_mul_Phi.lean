-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_integral_stieltjesPhase_eq_two_log_mul_Phi
-- name    : MetricCodes.Spherical.HigherHierarchy.integral_stieltjesPhase_eq_two_log_mul_Phi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:34.786068+00:00
-- url     : https://prove2.me/theorems/7f8fde8d-3b2c-4b2c-9ec1-daf4ae5321bd
-- title:
--   MetricCodes.Spherical.HigherHierarchy.integral_stieltjesPhase_eq_two_log_mul_Phi
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory
open scoped BigOperators Interval

theorem MetricCodes.Spherical.HigherHierarchy.integral_stieltjesPhase_eq_two_log_mul_Phi {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (μ : Measure ℝ)
    (hpositive : ∀ᵐ t ∂μ, 0 < t)
    (ha : ∀ i : Fin (r + 1),
      Integrable (stieltjesLogAtom (quadraticCoordinate (a i))) μ)
    (hb : ∀ i : Fin r,
      Integrable (stieltjesLogAtom (quadraticCoordinate (b i))) μ)
    (hma : ∀ i : Fin (r + 1),
      (∫ t : ℝ, stieltjesLogAtom (quadraticCoordinate (a i)) t ∂μ) =
        2 * Real.log 2 * MetricCodes.sphericalEntropy (a i))
    (hmb : ∀ i : Fin r,
      (∫ t : ℝ, stieltjesLogAtom (quadraticCoordinate (b i)) t ∂μ) =
        2 * Real.log 2 * MetricCodes.sphericalEntropy (b i)) :
    (∫ t : ℝ, stieltjesPhase a b t ∂μ) =
      2 * Real.log 2 * Phi a b := by sorry
