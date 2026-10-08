-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_center_ideal_power_annihilates_strict_jets
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_annihilates_strict_jets
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T06:30:15.905703+00:00
-- url     : https://prove2.me/theorems/5efbbbb5-420a-479d-ab4a-7b2217a55b50
-- title:
--   A logarithmic center ideal power annihilates strict weighted jets
-- statement:
--   Fix a center and let the logarithmic coordinate generators have multiplicities eᵢ. If a polynomial belongs to the nth power of the ideal they generate, then all its formal-jet coefficients of weighted degree below nR vanish, provided the coordinate truncation bounds hold and R ≤ eᵢvᵢ for each coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/CompactLogJetIdeal.lean; local-center case of the logarithmic ideal-power vanishing lemma

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_annihilates_strict_jets
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (v : Fin (m + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℝ) * v 0)
    (R : ℝ) (he : ∀ i, R ≤ (e i : ℝ) * v i)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ FormalInterpolation.logarithmicCenterIdeal c T e ^ n)
    (a : ↥(strictWeightedSimplex v ((n : ℝ) * R))) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
      (FormalInterpolation.formalJet c P) = 0 := by sorry
