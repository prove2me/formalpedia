-- Prove2me | Theorems.Thm_Malliavin_predictableDerivative_compBrownianD12
-- name    : Malliavin.predictableDerivative_compBrownianD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:32.391147+00:00
-- url     : https://prove2.me/theorems/a248055d-2cf2-411d-b41c-b9a730dacb71
-- title:
--   Malliavin: predictable Derivative comp Brownian D12
-- statement:
--   **The Clark--Ocone integrand of `g (B T)`** is the predictable projection of the textbook
--   derivative `g' (B T) 1_{(0, T]}(t)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L164-L176
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L164-L176

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

theorem Malliavin.predictableDerivative_compBrownianD12 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ K * Real.exp (c * |x|))
    (hgb' : ∀ x, |deriv g x| ≤ K * Real.exp (c * |x|)) (T : ℝ≥0) :
    predictableDerivative C
        (compBrownianD12 C.coordinate C.coordinate_apply hg hK hc hgb hgb' T) =
      predictableProjection 𝓕 (tensor (intervalIndicator T)
        ((memLp_deriv_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb' T).toLp _)) := by sorry
