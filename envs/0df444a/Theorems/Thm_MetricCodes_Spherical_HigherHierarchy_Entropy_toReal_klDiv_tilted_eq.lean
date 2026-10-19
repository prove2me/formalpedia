-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_toReal_klDiv_tilted_eq
-- name    : MetricCodes.Spherical.HigherHierarchy.Entropy.toReal_klDiv_tilted_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:33.730806+00:00
-- url     : https://prove2.me/theorems/5bbafb30-b77f-49d1-99d7-886f76d934eb
-- title:
--   MetricCodes.Spherical.HigherHierarchy.Entropy.toReal_klDiv_tilted_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Entropy

theorem MetricCodes.Spherical.HigherHierarchy.Entropy.toReal_klDiv_tilted_eq {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hμν : μ ≪ ν)
    (hfμ : Integrable f μ)
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hllr : Integrable (llr μ ν) μ) :
    (InformationTheory.klDiv μ (ν.tilted f)).toReal =
      (InformationTheory.klDiv μ ν).toReal - ∫ x, f x ∂μ +
        Real.log (∫ x, Real.exp (f x) ∂ν) := by sorry
