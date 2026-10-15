-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_truncation_preserves_filtered_substitution
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_truncation_preserves_filtered_substitution
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T18:21:54.43767+00:00
-- url     : https://prove2.me/theorems/271828a5-228e-4abd-ad6f-76c1928e5a2b
-- title:
--   Weighted truncation preserves filtered polynomial substitution
-- statement:
--   For any polynomial evaluated using positive-weight coordinates with one-variable power series corrections, replacing each correction by its truncation below degree T preserves vanishing of all coefficients below a strict weighted cutoff, provided the discarded tail has weight at least that of its coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_truncation_preserves_filtered_substitution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (c : Fin m → ℂ) (G : Fin m → PowerSeries ℂ) (T : Fin m → ℕ)
    (hT : ∀ i : Fin m, q i.succ ≤ (T i : ℝ) * q 0)
    (B : ℝ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPolynomial.aeval
          (Fin.cases (1 + MvPowerSeries.X 0)
            (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
              liftLogSeries m (G i))) P) = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a)
        (MvPolynomial.aeval
          (Fin.cases (1 + MvPolynomial.X 0)
            (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
              Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
                (PowerSeries.trunc (T i) (G i)))) P) = 0 := by sorry
