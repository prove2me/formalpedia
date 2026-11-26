-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnDeterministic_itoIntegral_deterministic_Ioc
-- name    : Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.itoIntegral_deterministic_Ioc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:30:37.615973+00:00
-- url     : https://prove2.me/theorems/61224aeb-c75b-537f-9015-7f13be227d62
-- title:
--   Is Brownian On Deterministic: ito Integral deterministic Ioc
-- statement:
--   On a deterministic interval integrand, Brownian compatibility gives the corresponding
--   Brownian increment.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L747-L755
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L747-L755

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.itoIntegral_deterministic_Ioc
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) {a b : ℝ≥0} (hab : a ≤ b) :
    C.itoIntegral (deterministicPredictableEmbedding 𝓕
      (indicatorConstLp 2 measurableSet_Ioc
        (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ))) =
      brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a := by sorry
