-- Prove2me | Theorems.Thm_GlobalTheory_norm_eisTerm_zero_le_of_near
-- name    : GlobalTheory.norm_eisTerm_zero_le_of_near
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:12:43.161572+00:00
-- url     : https://prove2.me/theorems/b73dde84-07c6-4df3-80da-9e0ac6cfd066
-- title:
--   Global Theory: norm eis Term zero le of near
-- statement:
--   The Global Theory construction uses the norm eis Term zero le of near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesLatticeDifferentiableOn.lean#L45-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesLatticeDifferentiableOn.lean#L45-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormFderivLeOfClosedBallSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open Metric Complex
open GlobalTheory
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem GlobalTheory.norm_eisTerm_zero_le_of_near {F : Type} [Field F] [NumberField F] {z z₀ : Emb F → ℂ} {r : ℝ}
    (hz₀ : z₀ ∈ upperHalf F) (hr : ∀ τ, 2 * r ≤ (z₀ τ).im) (hz : ‖z - z₀‖ < r) (k : ℕ) {p : F × F} (hp : p ≠ 0) :
    ‖eisTerm k 0 z p‖ ≤ (2 ^ Fintype.card (Emb F)) ^ k * ‖eisTerm k 0 z₀ p‖ := by sorry
