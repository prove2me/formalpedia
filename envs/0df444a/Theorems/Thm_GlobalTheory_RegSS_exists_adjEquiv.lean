-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_exists_adjEquiv
-- name    : GlobalTheory.RegSS.exists_adjEquiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:48.350038+00:00
-- url     : https://prove2.me/theorems/d4b41757-5784-47ec-9e75-1d9eaaabc601
-- title:
--   Reg SS: exists adj Equiv
-- statement:
--   The Reg SS construction uses the exists adj Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L654-L709
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L654-L709

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

theorem GlobalTheory.RegSS.exists_adjEquiv (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular σ J γ)
    (hA : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ) :
    ∃ τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) ≃ₐ[F]
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E),
      (∀ l, (τ l : Matrix n n E) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J (l : Matrix n n E)) ∧
      (∀ l, τ (τ l) = l) ∧
      (∀ e : E, τ (algebraMap E _ e) = algebraMap E _ (σ e)) ∧
      ∀ l, l ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix n n E) ↔ τ l = l := by sorry
