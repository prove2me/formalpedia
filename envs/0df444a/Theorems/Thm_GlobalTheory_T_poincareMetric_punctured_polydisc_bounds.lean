-- Prove2me | Theorems.Thm_GlobalTheory_T_poincareMetric_punctured_polydisc_bounds
-- name    : GlobalTheory.T.poincareMetric_punctured_polydisc_bounds
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:04.771462+00:00
-- url     : https://prove2.me/theorems/17e6d711-f422-4a4e-a3bb-c213e8840b28
-- title:
--   T: poincare Metric punctured polydisc bounds
-- statement:
--   The T construction uses the poincare Metric punctured polydisc bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBoundsStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBoundsStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBounds
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBoundsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.poincareMetric_punctured_polydisc_bounds : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 → ∀ z ∈ punctured ha ρ, (poincareGram a z).PosSemidef ∧ ∀ ξ : Fin n → ℂ, (∀ k, ‖ξ k‖ ≤ 2 * gnorm (poincareGram a z) ξ) ∧ ∀ i : Fin a, ‖ξ (Fin.castLE ha i)‖ ≤ 2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) * gnorm (poincareGram a z) ξ := by sorry
