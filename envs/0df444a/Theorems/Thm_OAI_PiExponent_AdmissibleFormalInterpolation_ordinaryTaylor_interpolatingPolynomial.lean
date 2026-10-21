-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_ordinaryTaylor_interpolatingPolynomial
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.ordinaryTaylor_interpolatingPolynomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:45:08.580119+00:00
-- url     : https://prove2.me/theorems/af163483-d7df-416e-9b9c-6e0d7febbb96
-- title:
--   Finite multivariate Taylor interpolation at distinct center–exponent pairs
-- statement:
--   For any selected pair in a finite family of distinct center–exponent pairs, there is a multivariate polynomial whose ordinary Taylor coefficient at that pair is one and whose coefficients at all other pairs in the family are zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.ordinaryTaylor_interpolatingPolynomial
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (center : ι → Fin (m + 1) → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (center x, exponent x)))
    (x : ι) :
    ∃ p : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ y : ι,
        (((MvPowerSeries.coeff (exponent y)).comp
          (MvPolynomial.aeval (fun i =>
            MvPowerSeries.C (center y i) + MvPowerSeries.X i)).toLinearMap) p) =
          if y = x then 1 else 0 := by sorry
