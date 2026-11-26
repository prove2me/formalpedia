-- Prove2me | Theorems.Thm_Malliavin_mderivD12_compPi
-- name    : Malliavin.mderivD12_compPi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:42:55.647+00:00
-- url     : https://prove2.me/theorems/014d9e21-f8a6-4c65-8009-7d498330d0df
-- title:
--   Malliavin: mderiv D12 comp Pi
-- statement:
--   The multivariate chain rule for the subtype map `mderivD12`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L888-L893
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L888-L893

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

theorem Malliavin.mderivD12_compPi {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (F : Fin n → D12 μ) :
    mderivD12 μ (D12.compPi μ hf hK F) =
      (memLp_grad_smul μ hf hK (fun i ↦ Lp.aestronglyMeasurable (F i : Lp ℝ 2 μ))
        (fun i ↦ mderivD12 μ (F i))).toLp _ := by sorry
