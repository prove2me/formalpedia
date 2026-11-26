-- Prove2me | Theorems.Thm_LowerSemicontinuous_lintegral_le_liminf
-- name    : LowerSemicontinuous.lintegral_le_liminf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:05:49.814194+00:00
-- url     : https://prove2.me/theorems/8f73900e-23e4-5787-9ba5-c4a9edb6263d
-- title:
--   Lower Semicontinuous: lintegral le liminf
-- statement:
--   Portmanteau-type liminf inequality for the lower Lebesgue integral of a lower
--   semicontinuous `ℝ≥0∞`-valued function: if `μ G ≤ liminf (μs · G)` for every open `G`,
--   then `∫⁻ f ∂μ ≤ liminf (∫⁻ f ∂(μs ·))`.
--
--   Reduces to `LowerSemicontinuous.lintegral_le_liminf_of_ne_top` via the truncations
--   `min f n` and monotone convergence.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LintegralLsc.lean#L107-L131
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LintegralLsc.lean#L107-L131

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal
variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [OpensMeasurableSpace W]

theorem LowerSemicontinuous.lintegral_le_liminf
    {μ : Measure W} {μs : ℕ → Measure W} {f : W → ℝ≥0∞}
    (hf : LowerSemicontinuous f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun i => μs i G) :
    ∫⁻ x, f x ∂μ ≤ atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) := by sorry
