-- Prove2me | Theorems.Thm_GaussianPerimeter_tendsto_no_success
-- name    : GaussianPerimeter.tendsto_no_success
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:13:32.455249+00:00
-- url     : https://prove2.me/theorems/9885976b-9cd3-4d9f-add2-7dcdcac919bb
-- title:
--   Gaussian Perimeter: tendsto no success
-- statement:
--   The probability of no success in independent trials has the Poisson limit
--   when the success probabilities vanish and the expected counts converge.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Basic.lean#L50-L66
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Basic.lean#L50-L66

module
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Order.LiminfLimsup
public import Definitions.Def_GaussianPerimeter_Basic
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter

theorem GaussianPerimeter.tendsto_no_success {q : ℕ → ℝ} {m : ℕ → ℕ} {c : ℝ}
    (hq : Tendsto q atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < q n)
    (hmq : Tendsto (fun n => (m n : ℝ) * q n) atTop (𝓝 c)) :
    Tendsto (fun n => (1 - q n) ^ m n) atTop (𝓝 (Real.exp (-c))) := by sorry
