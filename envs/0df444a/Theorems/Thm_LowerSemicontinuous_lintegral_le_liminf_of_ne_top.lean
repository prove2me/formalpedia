-- Prove2me | Theorems.Thm_LowerSemicontinuous_lintegral_le_liminf_of_ne_top
-- name    : LowerSemicontinuous.lintegral_le_liminf_of_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:05:56.940883+00:00
-- url     : https://prove2.me/theorems/72803146-70c7-4ef7-8b2d-3aad1dc5a30d
-- title:
--   Lower Semicontinuous: lintegral le liminf of ne top
-- statement:
--   Portmanteau-type liminf inequality for the lower Lebesgue integral of a lower
--   semicontinuous function with finite values: if `μ G ≤ liminf (μs · G)` for every open `G`,
--   then `∫⁻ f ∂μ ≤ liminf (∫⁻ f ∂(μs ·))`.
--
--   This is the `ℝ≥0∞`-valued analogue of
--   `MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`:
--   layer-cake formula + openness of superlevel sets + Fatou's lemma.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LintegralLsc.lean#L65-L99
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LintegralLsc.lean#L65-L99

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal
variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [OpensMeasurableSpace W]

theorem LowerSemicontinuous.lintegral_le_liminf_of_ne_top
    {μ : Measure W} {μs : ℕ → Measure W} {f : W → ℝ≥0∞}
    (hf : LowerSemicontinuous f) (hf_ne : ∀ x, f x ≠ ∞)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun i => μs i G) :
    ∫⁻ x, f x ∂μ ≤ atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) := by sorry
