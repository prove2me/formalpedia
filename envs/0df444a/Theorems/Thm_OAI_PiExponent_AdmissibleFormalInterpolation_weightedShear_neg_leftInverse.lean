-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_neg_leftInverse
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_neg_leftInverse
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T22:01:06.801807+00:00
-- url     : https://prove2.me/theorems/9c2102e6-29d2-448d-9ad9-6dfa50b1ecdf
-- title:
--   Cancellation of opposite shears on strict weighted coefficient jets
-- statement:
--   For positive weights and positive strict cutoff, suppose D_i vanishes below degree N_i and u_i ≤ N_i v0. The finite coefficient operators for translation by D and then -D compose to the identity linear map. Both translations preserve weight, so intermediate truncation is harmless. Equality in the weight bound is allowed, and weight exactly H is excluded. When m = 0 the operator is the identity; N_i = 0 is incompatible with the hypotheses.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_neg_leftInverse
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (hH : 0 < H) :
    (weightedShear (m := m) v0 u H (fun i : Fin m => -D i)) ∘ₗ
        (weightedShear (m := m) v0 u H D) =
      (LinearMap.id :
        ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) →ₗ[ℂ]
          ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ)) := by sorry
