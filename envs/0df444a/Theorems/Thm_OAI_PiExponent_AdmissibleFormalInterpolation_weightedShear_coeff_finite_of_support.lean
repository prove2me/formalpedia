-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_coeff_finite_of_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_coeff_finite_of_support
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T16:50:34.19601+00:00
-- url     : https://prove2.me/theorems/59027ddf-61c9-4b21-a6fd-42ac0df80aa2
-- title:
--   Finite coefficient expansion from monomial support
-- statement:
--   For a finite set of source exponents S, if every monomial outside S has zero coefficient at the chosen target exponent after shearing, then the coefficient of the sheared arbitrary formal series is the finite sum over S of the sheared monomial coefficients times the corresponding source coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_coeff_finite_of_support
    {m : ℕ} (S : Finset (Fin (m + 1) → ℕ))
    (delta : Fin m → PowerSeries ℂ)
    (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (a : ↥S)
    (hzero : ∀ b : Fin (m + 1) → ℕ, b ∉ S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
        (formalShear delta
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector b) 1)) = 0) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
            (fun i : Fin m =>
              MvPowerSeries.X i.succ + liftLogSeries m (delta i))) F) =
      ∑ b : ↥S,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
            (formalShear delta
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector b.val) 1)) *
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val) F := by sorry
