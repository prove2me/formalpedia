-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficient_functionals_independent
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficient_functionals_independent
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T08:44:24.737002+00:00
-- url     : https://prove2.me/theorems/08816769-d715-4ab5-8628-a40520da10d1
-- title:
--   Independence of distinct formal-jet coefficient functionals
-- statement:
--   For a finite injectively indexed family of center and exponent pairs, the corresponding formal-jet coefficient extraction maps are linearly independent linear functionals on the polynomial ring.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficient_functionals_independent
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    ∃ L : ι → MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ] ℂ,
      LinearIndependent ℂ L ∧
      ∀ x P, L x P =
        MvPowerSeries.coeff (exponent x) (formalJet (c x) P) := by sorry
