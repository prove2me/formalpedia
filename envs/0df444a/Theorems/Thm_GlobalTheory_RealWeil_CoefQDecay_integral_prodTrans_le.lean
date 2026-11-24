-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_integral_prodTrans_le
-- name    : GlobalTheory.RealWeil.CoefQDecay.integral_prodTrans_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:15:31.627795+00:00
-- url     : https://prove2.me/theorems/2beff062-a463-4393-96e9-9cad4126e621
-- title:
--   Coef QDecay: integral prod Trans le
-- statement:
--   The Coef QDecay construction uses the integral prod Trans le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecaySecondPart.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecaySecondPart.lean#L84-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
open scoped FourierTransform ContDiff RealInnerProductSpace Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.CoefQDecay
variable {n : ℕ}

theorem GlobalTheory.RealWeil.CoefQDecay.integral_prodTrans_le (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    ∫ x, ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖ ≤ ∫ x, derivBound g g' j x := by sorry
