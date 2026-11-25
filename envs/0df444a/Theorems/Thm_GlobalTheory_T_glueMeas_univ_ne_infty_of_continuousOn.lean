-- Prove2me | Theorems.Thm_GlobalTheory_T_glueMeas_univ_ne_infty_of_continuousOn
-- name    : GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:32:28.603912+00:00
-- url     : https://prove2.me/theorems/c31c5197-7c08-40b9-9579-a3939f7a1d11
-- title:
--   T: glue Meas univ ne infty of continuous On
-- statement:
--   The T construction uses the glue Meas univ ne infty of continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlueMeasUnivNeTopOfCompactStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlueMeasUnivNeTopOfCompactStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueMeasUnivNeTopOfCompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueMeasUnivNeTopOfCompactStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ} {ι : Type} (e : ι → OpenPartialHomeomorph M (V n)), (∀ y, ∃ i, y ∈ (e i).source) → (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → ∀ (r : ι → V n → ℝ), (∀ i, ContinuousOn (r i) (e i).target) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → r i (e i y) = ‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2 * r j (e j y)) → GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) univ ≠ ∞ := by sorry
