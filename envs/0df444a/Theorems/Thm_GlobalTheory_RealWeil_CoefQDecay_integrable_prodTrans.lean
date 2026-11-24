-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_integrable_prodTrans
-- name    : GlobalTheory.RealWeil.CoefQDecay.integrable_prodTrans
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:31.718597+00:00
-- url     : https://prove2.me/theorems/2c18e2fb-6078-4699-ac13-34ff3e26cc5f
-- title:
--   Coef QDecay: integrable prod Trans
-- statement:
--   The Coef QDecay construction uses the integrable prod Trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecaySecondPart.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecaySecondPart.lean#L76-L82

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

theorem GlobalTheory.RealWeil.CoefQDecay.integrable_prodTrans (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    Integrable (fun x => ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖) := by sorry
