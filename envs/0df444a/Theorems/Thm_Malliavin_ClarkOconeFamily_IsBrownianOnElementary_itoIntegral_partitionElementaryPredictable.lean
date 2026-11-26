-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnElementary_itoIntegral_partitionElementaryPredictable
-- name    : Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_partitionElementaryPredictable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:31:07.941716+00:00
-- url     : https://prove2.me/theorems/86498c73-b924-57e0-a40a-6b8c8cdaa0e3
-- title:
--   Is Brownian On Elementary: ito Integral partition Elementary Predictable
-- statement:
--   Elementary Brownian compatibility evaluates the designated Itô integral on every adapted
--   step process carried by a partition.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L283-L292
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L283-L292

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto
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

theorem Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_partitionElementaryPredictable
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    C.itoIntegral (partitionElementaryPredictable Q Z) =
      C.partitionElementaryIntegralValue Q Z := by sorry
