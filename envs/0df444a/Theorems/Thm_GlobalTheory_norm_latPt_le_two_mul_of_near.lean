-- Prove2me | Theorems.Thm_GlobalTheory_norm_latPt_le_two_mul_of_near
-- name    : GlobalTheory.norm_latPt_le_two_mul_of_near
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:55.066103+00:00
-- url     : https://prove2.me/theorems/5fa7e018-a232-4d6c-9453-bf5b039d0c4e
-- title:
--   Global Theory: norm lat Pt le two mul of near
-- statement:
--   The Global Theory construction uses the norm lat Pt le two mul of near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesLatticeDifferentiableOn.lean#L16-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesLatticeDifferentiableOn.lean#L16-L43

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

theorem GlobalTheory.norm_latPt_le_two_mul_of_near {F : Type} [Field F] [NumberField F] {z z₀ : Emb F → ℂ} {r : ℝ}
    (hr : ∀ τ, 2 * r ≤ (z₀ τ).im) (hz : ‖z - z₀‖ < r) (p : F × F) (τ : Emb F) :
    ‖latPt z₀ p τ‖ ≤ 2 * ‖latPt z p τ‖ := by sorry
