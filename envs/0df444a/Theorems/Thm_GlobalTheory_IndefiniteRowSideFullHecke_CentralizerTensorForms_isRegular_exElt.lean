-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CentralizerTensorForms_isRegular_exElt
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.isRegular_exElt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:35.159804+00:00
-- url     : https://prove2.me/theorems/fc1e93a8-cd43-46d1-93fa-9d3eda22d132
-- title:
--   Centralizer Tensor Forms: is Regular ex Elt
-- statement:
--   The Centralizer Tensor Forms construction uses the is Regular ex Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/CentralizerTensorForms.lean#L265-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/CentralizerTensorForms.lean#L265-L281

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

theorem GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.isRegular_exElt :
    IsRegular (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) exElt := by sorry
