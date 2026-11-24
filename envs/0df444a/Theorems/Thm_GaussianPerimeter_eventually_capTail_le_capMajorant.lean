-- Prove2me | Theorems.Thm_GaussianPerimeter_eventually_capTail_le_capMajorant
-- name    : GaussianPerimeter.eventually_capTail_le_capMajorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:33:50.82995+00:00
-- url     : https://prove2.me/theorems/ade7b028-8f61-423e-9dac-9c031849894f
-- title:
--   Gaussian Perimeter: eventually cap Tail le cap Majorant
-- statement:
--   The Gaussian Perimeter construction uses the eventually cap Tail le cap Majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean#L370-L373
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean#L370-L373

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter

theorem GaussianPerimeter.eventually_capTail_le_capMajorant (a w : ℝ) (ha : 0 < a) :
    ∀ᶠ n in atTop, capTail n (capThreshold a n w) ≤ capMajorant a n w := by sorry
