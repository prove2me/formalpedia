-- Prove2me | Theorems.Thm_Malliavin_isTotal_of_dense_span
-- name    : Malliavin.isTotal_of_dense_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:44.803124+00:00
-- url     : https://prove2.me/theorems/2d513273-79a2-4724-bf5b-c0a40178441e
-- title:
--   Malliavin: is Total of dense span
-- statement:
--   A family whose span is dense is total.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L106-L118
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L106-L118

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {E F ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem Malliavin.isTotal_of_dense_span (T : κ → F)
    (hT : Dense (Submodule.span ℝ (Set.range T) : Set F)) : IsTotal T := by sorry
