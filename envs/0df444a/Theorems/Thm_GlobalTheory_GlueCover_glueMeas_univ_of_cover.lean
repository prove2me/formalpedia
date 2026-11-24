-- Prove2me | Theorems.Thm_GlobalTheory_GlueCover_glueMeas_univ_of_cover
-- name    : GlobalTheory.GlueCover.glueMeas_univ_of_cover
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:01.056802+00:00
-- url     : https://prove2.me/theorems/e3990fac-5de6-4e09-8818-b5127da27cfc
-- title:
--   Glue Cover: glue Meas univ of cover
-- statement:
--   The Glue Cover construction uses the glue Meas univ of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormula.lean#L251-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormula.lean#L251-L270

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
open GlobalTheory GlobalTheory.GlueCover
open GlobalTheory.ChartGlue
variable {n : ℕ}

theorem GlobalTheory.GlueCover.glueMeas_univ_of_cover : ∀ (n : ℕ), n ≠ 0 → ∀ (A B ι κ : Type) [TopologicalSpace A]
    [TopologicalSpace B] [T2Space A] [T2Space B] [SecondCountableTopology A]
    [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B]
    [BorelSpace B] (e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (ρ : ι → A → ℝ≥0∞)
    (e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)) (ρ' : κ → B → ℝ≥0∞),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j)) →
    (∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y) →
    (∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j)) →
    (∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y) →
    ∀ (m : B → A), Continuous m → ∀ T : Set A, T.Finite → (m ⁻¹' T).Finite → ∀ d : ℕ, d ≠ 0 →
    (∀ x ∉ T, (m ⁻¹' {x}).encard = d) →
    (∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) →
    GlobalTheory.ChartGlue.glueMeas e' ρ' Set.univ = d * GlobalTheory.ChartGlue.glueMeas e ρ Set.univ := by sorry
