-- Prove2me | Theorems.Thm_GaussianPerimeter_shiftedCapTail_measurable
-- name    : GaussianPerimeter.shiftedCapTail_measurable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:09:47.633805+00:00
-- url     : https://prove2.me/theorems/34f48bd4-cb32-409b-83cb-0c10f8ec2088
-- title:
--   Gaussian Perimeter: shifted Cap Tail measurable
-- statement:
--   The Gaussian Perimeter construction uses the shifted Cap Tail measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/NazarovLimit.lean#L57-L69
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/NazarovLimit.lean#L57-L69

module
public import Definitions.Def_GaussianPerimeter_LimitBound
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_GaussianPerimeter_NazarovLimit
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter

theorem GaussianPerimeter.shiftedCapTail_measurable (a : ℝ) (n : ℕ) : Measurable (shiftedCapTail a n) := by sorry
