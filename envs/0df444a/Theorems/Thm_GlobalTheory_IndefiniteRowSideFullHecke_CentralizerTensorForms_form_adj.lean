-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CentralizerTensorForms_form_adj
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form_adj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:09.127018+00:00
-- url     : https://prove2.me/theorems/6b7a462c-4177-54d1-9e1a-fce72226a285
-- title:
--   Centralizer Tensor Forms: form adj
-- statement:
--   The Centralizer Tensor Forms construction uses the form adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/CentralizerTensorForms.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/CentralizerTensorForms.lean#L61-L73

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
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
open Matrix NumberField
open scoped TensorProduct
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form_adj (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (l : Matrix n n A) (y y' : n → A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form σ J y (l *ᵥ y') =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form σ J (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J l *ᵥ y) y' := by sorry
