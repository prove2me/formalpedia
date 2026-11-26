-- Prove2me | Theorems.Thm_Malliavin_simpleDiv_one
-- name    : Malliavin.simpleDiv_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:10.913814+00:00
-- url     : https://prove2.me/theorems/8b6cb203-7149-5152-a235-7a563fa8e620
-- title:
--   Malliavin: simple Div one
-- statement:
--   The Malliavin construction uses the simple Div one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1340-L1347
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1340-L1347

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

theorem Malliavin.simpleDiv_one (h : Space μ) :
    simpleDiv μ (⟨fun _ ↦ 1, IsSmoothBounded.const 1⟩, h) = (h : Lp ℝ 2 μ) := by sorry
