-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralConstruction_positiveIteratedTowerLI_surjective_of_generated
-- name    : Malliavin.IteratedIntegralConstruction.positiveIteratedTowerLI_surjective_of_generated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:58:41.061208+00:00
-- url     : https://prove2.me/theorems/05b1d05b-43b6-405c-82ee-909a32fd85af
-- title:
--   Iterated Integral Construction: positive Iterated Tower LI surjective of generated
-- statement:
--   If the Brownian coordinates generate a second-countable ambient `L²` space, the selected
--   law-level tower exhausts its centered part.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1144-L1150
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1144-L1150

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
open ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace lp
variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}
open Malliavin.IteratedIntegralConstruction
attribute [local instance] Malliavin.IteratedIntegralConstruction.fact_two_ne_top
attribute [local instance] Malliavin.IteratedIntegralConstruction.simplexBasisIndex_countable
attribute [local instance] Malliavin.IteratedIntegralConstruction.globalBasisIndex_infinite

theorem Malliavin.IteratedIntegralConstruction.positiveIteratedTowerLI_surjective_of_generated
    (hB : IsPreBrownianReal B P) [SecondCountableTopology (RandomL2 P)]
    (hgen : IsWienerGenerated B) :
    Function.Surjective (positiveIteratedTowerLI hB) := by sorry
