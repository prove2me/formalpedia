-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_plusTensor_tConj
-- name    : GlobalTheory.RegSS.plusTensor_tConj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:57.423438+00:00
-- url     : https://prove2.me/theorems/9d60b1e5-954d-54bf-9c5f-6a00a43cea47
-- title:
--   Reg SS: plus Tensor t Conj
-- statement:
--   The Reg SS construction uses the plus Tensor t Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L716-L742
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L716-L742

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}
open Matrix NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}

theorem GlobalTheory.RegSS.plusTensor_tConj (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular σ J γ)
    (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix n n E) ⊗[F] E) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusTensor σ J (γ : Matrix n n E)
        (_root_.GlobalTheory.RegSS.tConj _ σ x) : Matrix n n E) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J
        (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusTensor σ J (γ : Matrix n n E) x : Matrix n n E) := by sorry
