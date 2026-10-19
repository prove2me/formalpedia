-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_diagonal_coeff_succ_shear_product
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.diagonal_coeff_succ_shear_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T16:32:34.890737+00:00
-- url     : https://prove2.me/theorems/7bf8a948-4125-4373-9be2-b5a1975372ae
-- title:
--   Diagonal coefficient of a finite product of sheared variables
-- statement:
--   For any finitely supported exponent and any family of univariate power series, the coefficient at that exponent in the product of the corresponding sheared variable powers is one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.diagonal_coeff_succ_shear_product
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff e
      (e.prod fun j k =>
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (delta i)) j) ^ k) = 1 := by sorry
