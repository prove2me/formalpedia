-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_coeff_of_successor_top_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_of_successor_top_support
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T16:51:45.304971+00:00
-- url     : https://prove2.me/theorems/67717e4e-063e-44db-bcfe-97d08b0135eb
-- title:
--   Shear coefficient at a top successor exponent
-- statement:
--   For a polynomial whose supported exponents do not exceed a target in any successor coordinate, and whose only supported exponent attaining all those successor bounds is the target itself, the sheared coefficient at the target is the original coefficient there times the zeroth-coordinate coefficient of the corresponding power of X.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_of_successor_top_support
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hbound : ∀ a ∈ P.support, ∀ i : Fin m, a i.succ ≤ e i.succ)
    (htop : ∀ a ∈ P.support, (∀ i : Fin m, a i.succ = e i.succ) → a = e) :
    MvPowerSeries.coeff e (formalShear delta P) =
      MvPolynomial.coeff e P *
        PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (e 0)) := by sorry
