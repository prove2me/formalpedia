-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralConstruction_hasSum_simplexIntegralLI
-- name    : Malliavin.IteratedIntegralConstruction.hasSum_simplexIntegralLI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:45.349611+00:00
-- url     : https://prove2.me/theorems/6ea8850b-8b9b-5067-a3ab-b3e8e8c7c430
-- title:
--   Iterated Integral Construction: has Sum simplex Integral LI
-- statement:
--   A vector in the positive kernel Hilbert sum is the sum of its orderwise selected simplex
--   images.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1175-L1186
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1175-L1186

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

theorem Malliavin.IteratedIntegralConstruction.hasSum_simplexIntegralLI (hB : IsPreBrownianReal B P) (f : PositiveKernelSum) :
    HasSum (fun n ↦ simplexIntegralLI hB n (f n))
      ((positiveIteratedTowerLI hB f : CenteredRandomL2 hB) : RandomL2 P) := by sorry
