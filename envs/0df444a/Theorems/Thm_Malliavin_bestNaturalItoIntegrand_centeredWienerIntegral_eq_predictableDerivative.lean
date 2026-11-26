-- Prove2me | Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredWienerIntegral_eq_predictableDerivative
-- name    : Malliavin.bestNaturalItoIntegrand_centeredWienerIntegral_eq_predictableDerivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:19.804366+00:00
-- url     : https://prove2.me/theorems/d569e9b5-0314-56fa-8be7-e13e528d845d
-- title:
--   Malliavin: best Natural Ito Integrand centered Wiener Integral eq predictable Derivative
-- statement:
--   Equivalently, on a Wiener-integral `D12` functional the canonical best integrand agrees with
--   the `predictableDerivative` used in the abstract Clark--Ocone statement.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L136-L146
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L136-L146

import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalItoDuality
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.bestNaturalItoIntegrand_centeredWienerIntegral_eq_predictableDerivative
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓅)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    bestNaturalItoIntegrand C.isPreBrownian C.stronglyMeasurable
        C.naturalFiltration (centeredWienerIntegral C.isPreBrownian g) =
      predictableDerivative C
        (wienerIntegralD12 C.isPreBrownian C.coordinate
          C.coordinate_apply C.generated g) := by sorry
