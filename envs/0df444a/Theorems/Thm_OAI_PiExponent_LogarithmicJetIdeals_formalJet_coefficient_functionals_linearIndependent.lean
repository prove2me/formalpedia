-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficient_functionals_linearIndependent
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficient_functionals_linearIndependent
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T00:09:23.305532+00:00
-- url     : https://prove2.me/theorems/f0034904-02d2-4901-b435-ad509bf4a1f6
-- title:
--   Independence of formal-jet coefficient requests
-- statement:
--   For a finite injective family of center/exponent pairs, the functionals taking a polynomial to its requested formalJet coefficient are linearly independent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficient_functionals_linearIndependent
    {m : ℕ} {ι : Type} [Fintype ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    LinearIndependent ℂ
      (fun x =>
        ({ toFun := fun P : MvPolynomial (Fin (m + 1)) ℂ =>
              MvPowerSeries.coeff (exponent x) (formalJet (c x) P)
           map_add' := by simp [formalJet]
           map_smul' := by simp [formalJet] } :
          MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ] ℂ)) := by sorry
