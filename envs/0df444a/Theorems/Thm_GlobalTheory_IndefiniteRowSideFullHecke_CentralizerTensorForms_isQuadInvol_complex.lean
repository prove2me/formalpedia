-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CentralizerTensorForms_isQuadInvol_complex
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.isQuadInvol_complex
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:28.041044+00:00
-- url     : https://prove2.me/theorems/10c5bb46-5687-47b8-b940-1c57b387cb71
-- title:
--   Centralizer Tensor Forms: is Quad Invol complex
-- statement:
--   The Centralizer Tensor Forms construction uses the is Quad Invol complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/CentralizerTensorForms.lean#L252-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/CentralizerTensorForms.lean#L252-L257

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.isQuadInvol_complex : IsQuadInvol ℝ ℂ (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) := by sorry
