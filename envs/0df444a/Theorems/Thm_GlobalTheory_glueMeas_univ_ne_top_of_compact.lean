-- Prove2me | Theorems.Thm_GlobalTheory_glueMeas_univ_ne_top_of_compact
-- name    : GlobalTheory.glueMeas_univ_ne_top_of_compact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:34.085673+00:00
-- url     : https://prove2.me/theorems/77a3c7b4-1903-4345-a56a-983703c5ef16
-- title:
--   Global Theory: glue Meas univ ne top of compact
-- statement:
--   The Global Theory construction uses the glue Meas univ ne top of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlueMeasUnivNeTopOfCompact.lean#L9-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlueMeasUnivNeTopOfCompact.lean#L9-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueMeasUnivNeTopOfCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.glueMeas_univ_ne_top_of_compact {M : Type} [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ} {ι : Type}
    (e : ι → OpenPartialHomeomorph M (V n)) (hcov : ∀ y, ∃ i, y ∈ (e i).source)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source))
    (r : ι → V n → ℝ) (hr : ∀ i, ContinuousOn (r i) (e i).target)
    (hc : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      r i (e i y) = ‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2 * r j (e j y)) :
    GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) univ ≠ ∞ := by sorry
