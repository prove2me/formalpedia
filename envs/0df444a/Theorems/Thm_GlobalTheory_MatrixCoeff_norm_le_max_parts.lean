-- Prove2me | Theorems.Thm_GlobalTheory_MatrixCoeff_norm_le_max_parts
-- name    : GlobalTheory.MatrixCoeff.norm_le_max_parts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:21:38.250007+00:00
-- url     : https://prove2.me/theorems/8833163d-2379-43e4-a205-800e5a4837f1
-- title:
--   Matrix Coeff: norm le max parts
-- statement:
--   The Matrix Coeff construction uses the norm le max parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffContinuousRapidDecay.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffContinuousRapidDecay.lean#L12-L20

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

theorem GlobalTheory.MatrixCoeff.norm_le_max_parts (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) : ‖w‖ ≤ max ‖pPart w‖ ‖qPart w‖ := by sorry
