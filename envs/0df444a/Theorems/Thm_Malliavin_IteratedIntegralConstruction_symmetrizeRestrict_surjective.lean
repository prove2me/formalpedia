-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralConstruction_symmetrizeRestrict_surjective
-- name    : Malliavin.IteratedIntegralConstruction.symmetrizeRestrict_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:36.790857+00:00
-- url     : https://prove2.me/theorems/4d9e0ee3-080e-42d6-86c5-d1b38ef40eea
-- title:
--   Iterated Integral Construction: symmetrize Restrict surjective
-- statement:
--   Every square-integrable simplex kernel is the simplex restriction of a symmetric product
--   kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L701-L703
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L701-L703

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

theorem Malliavin.IteratedIntegralConstruction.symmetrizeRestrict_surjective (n : ℕ) :
    Function.Surjective (symmetrizeRestrict n) := by sorry
