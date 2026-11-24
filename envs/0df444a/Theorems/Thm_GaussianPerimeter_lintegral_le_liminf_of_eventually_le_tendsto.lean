-- Prove2me | Theorems.Thm_GaussianPerimeter_lintegral_le_liminf_of_eventually_le_tendsto
-- name    : GaussianPerimeter.lintegral_le_liminf_of_eventually_le_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:13:48.886874+00:00
-- url     : https://prove2.me/theorems/d22866ce-6f01-4a2d-8b28-90b0408da983
-- title:
--   Gaussian Perimeter: lintegral le liminf of eventually le tendsto
-- statement:
--   Fatou's lemma applied to lower bounds that hold eventually at each point.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Basic.lean#L69-L78
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Basic.lean#L69-L78

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

theorem GaussianPerimeter.lintegral_le_liminf_of_eventually_le_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n))
    (hg : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (F x)))
    (hgf : ∀ x, ∀ᶠ n in atTop, g n x ≤ f n x) :
    (∫⁻ x, F x ∂μ) ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := by sorry
