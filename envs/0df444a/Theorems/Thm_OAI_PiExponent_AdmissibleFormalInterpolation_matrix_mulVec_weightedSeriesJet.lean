-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_matrix_mulVec_weightedSeriesJet
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.matrix_mulVec_weightedSeriesJet
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:31:34.733769+00:00
-- url     : https://prove2.me/theorems/4a7e3139-dcbc-4966-885f-dd0e6b8ff85c
-- title:
--   Matrix column combinations are weighted polynomial jet coefficients
-- statement:
--   Every column coefficient vector determines a weighted polynomial whose jet coefficients under arbitrary polynomial substitutions equal the matrix-vector product. Construct the polynomial by summing the column monomials with the supplied coefficients. Its support stays within the column simplex, so no positivity assumptions are needed. Empty column sets give the zero polynomial, and empty row sets impose no coefficient conditions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedSeriesJets

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.matrix_mulVec_weightedSeriesJet
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : InterpolationMatrix.Column w0 w H → ℂ) :
    ∃ P : WeightedPolynomial w0 w H,
      ∀ rho : InterpolationMatrix.Row K v0 theta w H,
        weightedSeriesJet v0 (fun i => w i / theta) H
          (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ)) P.val rho.2 =
        ((InterpolationMatrix.matrix K w0 v0 theta w H r G).mulVecLin x) rho := by sorry
