-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CentralizerTensorForms_adj_eq_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj_eq_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:16:44.881504+00:00
-- url     : https://prove2.me/theorems/3840db45-b63d-4c2f-899b-e76c822f9de3
-- title:
--   Centralizer Tensor Forms: adj eq iff
-- statement:
--   The Centralizer Tensor Forms construction uses the adj eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/CentralizerTensorForms.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/CentralizerTensorForms.lean#L38-L47

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj_eq_iff (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (l m : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J l = m ↔ _root_.Formalism.UG.cT σ l * J = J * m := by sorry
