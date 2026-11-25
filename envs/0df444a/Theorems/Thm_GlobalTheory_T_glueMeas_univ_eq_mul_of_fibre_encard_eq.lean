-- Prove2me | Theorems.Thm_GlobalTheory_T_glueMeas_univ_eq_mul_of_fibre_encard_eq
-- name    : GlobalTheory.T.glueMeas_univ_eq_mul_of_fibre_encard_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:32:30.485249+00:00
-- url     : https://prove2.me/theorems/d32a347a-5e45-4c4d-93a3-861d067b595d
-- title:
--   T: glue Meas univ eq mul of fibre encard eq
-- statement:
--   The T construction uses the glue Meas univ eq mul of fibre encard eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormulaStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormulaStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormulaStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.glueMeas_univ_eq_mul_of_fibre_encard_eq : ∀ (n : ℕ), n ≠ 0 → ∀ (A B ι κ : Type) [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B] [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] (e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (ρ : ι → A → ℝ≥0∞) (e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)) (ρ' : κ → B → ℝ≥0∞), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j)) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j)) → (∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source → ρ' i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y) → ∀ (m : B → A), Continuous m → ∀ T : Set A, T.Finite → (m ⁻¹' T).Finite → ∀ d : ℕ, d ≠ 0 → (∀ x ∉ T, (m ⁻¹' {x}).encard = d) → (∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source, m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) → GlobalTheory.ChartGlue.glueMeas e' ρ' Set.univ = d * GlobalTheory.ChartGlue.glueMeas e ρ Set.univ := by sorry
