-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CentralizerTensorForms_hform_eq
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:30.015804+00:00
-- url     : https://prove2.me/theorems/54c24fae-918e-4549-a5e5-23d6ddbe9af8
-- title:
--   Centralizer Tensor Forms: hform eq
-- statement:
--   The Centralizer Tensor Forms construction uses the hform eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/CentralizerTensorForms.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/CentralizerTensorForms.lean#L52-L55

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq (σ : A →+* A) (J : Matrix n n A) (x y : n → A) :
    _root_.Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by sorry
