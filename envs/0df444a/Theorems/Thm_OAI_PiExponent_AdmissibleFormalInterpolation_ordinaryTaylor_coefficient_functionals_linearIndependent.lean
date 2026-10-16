-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_ordinaryTaylor_coefficient_functionals_linearIndependent
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.ordinaryTaylor_coefficient_functionals_linearIndependent
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:39:21.221201+00:00
-- url     : https://prove2.me/theorems/38eaaef6-9a9a-4e36-a65d-be345a5f5293
-- title:
--   Independence of ordinary multivariate Taylor coefficient functionals
-- statement:
--   Ordinary multivariate Taylor coefficient functionals on polynomials are linearly independent whenever their center–exponent pairs are distinct.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.ordinaryTaylor_coefficient_functionals_linearIndependent
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (center : ι → Fin (m + 1) → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (center x, exponent x))) :
    LinearIndependent ℂ
      (fun x => (MvPowerSeries.coeff (exponent x)).comp
        (MvPolynomial.aeval (fun i =>
          MvPowerSeries.C (center x i) + MvPowerSeries.X i)).toLinearMap) := by sorry
