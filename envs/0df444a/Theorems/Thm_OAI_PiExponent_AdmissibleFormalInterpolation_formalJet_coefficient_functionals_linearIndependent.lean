-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalJet_coefficient_functionals_linearIndependent
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalJet_coefficient_functionals_linearIndependent
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T09:28:03.233136+00:00
-- url     : https://prove2.me/theorems/65f7d05e-622e-4c6a-8918-91e1cd5e2076
-- title:
--   Independence of distinct formal-jet coefficient functionals
-- statement:
--   If the center–exponent pairs are distinct, the corresponding formal-jet coefficient functionals on multivariate polynomials are linearly independent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalJet_coefficient_functionals_linearIndependent
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    LinearIndependent ℂ
      (fun x => (MvPowerSeries.coeff (exponent x)).comp
        (formalJet (c x)).toLinearMap) := by sorry
