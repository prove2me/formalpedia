-- Prove2me | Theorems.Thm_Malliavin_IsWienerGenerated_measurable
-- name    : Malliavin.IsWienerGenerated.measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:48:51.826245+00:00
-- url     : https://prove2.me/theorems/4a1628e3-afeb-5e01-a028-c205f0e0c347
-- title:
--   Is Wiener Generated: measurable
-- statement:
--   Every coordinate is measurable when the process generates the ambient sigma-algebra.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L408-L412
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L408-L412

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

theorem Malliavin.IsWienerGenerated.measurable (hgen : IsWienerGenerated B) (t : ℝ≥0) :
    Measurable (B t) := by sorry
