-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_finsum_cutoff
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weighted_finsum_cutoff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:10:19.981352+00:00
-- url     : https://prove2.me/theorems/cae8ec56-4b22-4c28-9e7d-62c54475eef1
-- title:
--   Weight triangularity truncates the shear coefficient expansion
-- statement:
--   Positive weights and weight triangularity force every monomial contribution from outside the strict weighted simplex to vanish at b. Prove that weight below H implies membership by the coordinate bounds a i ≤ floor(H / w i), then restrict the finsum to this finite set. Equality at weight H is excluded, and still gives strictly larger weight than b. The zero-constant hypothesis is retained for compatibility, although this cutoff argument does not use it.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weighted_finsum_cutoff
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (D : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i) (hH : 0 < H)
    (hD0 : ∀ i, PowerSeries.coeff 0 (D i) = 0)
    (htri : ∀ (a b : Fin (m + 1) → ℕ),
      (∑ i, Fin.cases v0 u i * (b i : ℝ)) <
        (∑ i, Fin.cases v0 u i * (a i : ℝ)) →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (seriesShear D
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0)
    (G : MvPowerSeries (Fin (m + 1)) ℂ)
    (b : ↥(strictWeightedSimplex (Fin.cases v0 u) H)) :
    (∑ᶠ a : Fin (m + 1) → ℕ,
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) G *
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (seriesShear D
            (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1))) =
      (∑ a : ↥(strictWeightedSimplex (Fin.cases v0 u) H),
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val) G *
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
            (seriesShear D
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) 1))) := by sorry
