-- Prove2me | Theorems.Thm_Malliavin_clarkOcone_comp_brownian
-- name    : Malliavin.clarkOcone_comp_brownian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:01.807076+00:00
-- url     : https://prove2.me/theorems/0f3b1cc5-d005-5b45-8b2a-03b9d89667af
-- title:
--   Malliavin: clark Ocone comp brownian
-- statement:
--   **Clark--Ocone for `g (B T)`**:
--   `g (B T) = E[g (B T)] + C.itoIntegral (Π (g' (B T) 1_{(0, T]}))`, where `Π` is the predictable
--   projection.  Reading `Π (g' (B T) 1_{(0, T]})` timewise as `E[g' (B T) | 𝓕ₜ] 1_{t ≤ T}` is the
--   pointwise identification not yet part of the contract.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L182-L193
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L182-L193

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

theorem Malliavin.clarkOcone_comp_brownian {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ K * Real.exp (c * |x|))
    (hgb' : ∀ x, |deriv g x| ≤ K * Real.exp (c * |x|)) (T : ℝ≥0) :
    (memLp_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb T).toLp _ =
      expectationL2 ((memLp_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb T).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (tensor (intervalIndicator T)
          ((memLp_deriv_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb' T).toLp
            _))) := by sorry
