-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_norm_iteratedFDeriv_prodTrans_le
-- name    : GlobalTheory.RealWeil.CoefQDecay.norm_iteratedFDeriv_prodTrans_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:32.13841+00:00
-- url     : https://prove2.me/theorems/902f083d-62ca-41d7-a2c6-cfa7169ac8d7
-- title:
--   Coef QDecay: norm iterated FDeriv prod Trans le
-- statement:
--   The Coef QDecay construction uses the norm iterated FDeriv prod Trans le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecaySecondPart.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecaySecondPart.lean#L47-L67

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

theorem GlobalTheory.RealWeil.CoefQDecay.norm_iteratedFDeriv_prodTrans_le (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖ ≤ derivBound g g' j x := by sorry
