-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_coeff_vanish_from_generators
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_coeff_vanish_from_generators
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T00:00:10.304102+00:00
-- url     : https://prove2.me/theorems/481bd873-89f6-49e2-8daa-8a8654754ff7
-- title:
--   A weighted coefficient bound passes from generators to their ideal
-- statement:
--   If every local jet-ideal generator has zero formal-jet coefficients below the weighted cutoff, then every polynomial in the ideal has the same vanishing property.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_coeff_vanish_from_generators
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hweights : ∀ j : Fin (m + 1), 0 < InterpolationMatrix.rowWeights v0 theta w j)
    (hgen : ∀ b : Fin (m + 1) → ℕ,
      (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) < R →
      ∀ i : Fin (m + 1),
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
          (AdmissibleFormalInterpolation.formalJet c (jetCoordinate c T i ^ e i)) = 0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : Q ∈ localJetIdeal c T e)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (a j : ℝ)) < R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet c Q) = 0 := by sorry
