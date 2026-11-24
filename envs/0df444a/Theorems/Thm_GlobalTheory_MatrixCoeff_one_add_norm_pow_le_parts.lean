-- Prove2me | Theorems.Thm_GlobalTheory_MatrixCoeff_one_add_norm_pow_le_parts
-- name    : GlobalTheory.MatrixCoeff.one_add_norm_pow_le_parts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:21:31.154321+00:00
-- url     : https://prove2.me/theorems/a23187b0-0989-4410-b90d-d0ed8e9f7643
-- title:
--   Matrix Coeff: one add norm pow le parts
-- statement:
--   The Matrix Coeff construction uses the one add norm pow le parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffContinuousRapidDecay.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffContinuousRapidDecay.lean#L22-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecayFirstPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffContinuousRapidDecay
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
open GlobalTheory
open GlobalTheory.MatrixCoeff

theorem GlobalTheory.MatrixCoeff.one_add_norm_pow_le_parts (n N : ℕ) (w : Fin n ⊕ Fin n → ℝ) :
    (1 + ‖w‖) ^ N ≤ (1 + ‖pPart w‖) ^ N + (1 + ‖qPart w‖) ^ N := by sorry
