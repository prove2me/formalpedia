-- Prove2me | Theorems.Thm_GlobalTheory_GlueCover_exists_sheet
-- name    : GlobalTheory.GlueCover.exists_sheet
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:55:26.528282+00:00
-- url     : https://prove2.me/theorems/5ed79efe-c0af-42ce-9c30-a50a7317a898
-- title:
--   Glue Cover: exists sheet
-- statement:
--   The Glue Cover construction uses the exists sheet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormula.lean#L72-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormula.lean#L72-L133

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
variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}
set_option autoImplicit false
open MeasureTheory Set Topology
open scoped ENNReal
variable {n : ℕ}
variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}
omit [T2Space A] [T2Space B]

theorem GlobalTheory.GlueCover.exists_sheet
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {z : B}
    (hch : ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {U : Set B} (hUo : IsOpen U) (hzU : z ∈ U) :
    ∃ M : Set B, M ⊆ U ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        _root_.GlobalTheory.ChartGlue.glueMeas e' ρ' (M ∩ m ⁻¹' Q) = _root_.GlobalTheory.ChartGlue.glueMeas e ρ Q := by sorry
