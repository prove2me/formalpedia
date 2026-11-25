-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_adj_map
-- name    : GlobalTheory.RegSS.adj_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:57.476847+00:00
-- url     : https://prove2.me/theorems/a8140d2c-5bde-4b39-ba59-a4ca717fb3ab
-- title:
--   Reg SS: adj map
-- statement:
--   The Reg SS construction uses the adj map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L393-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L393-L403

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
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
open Matrix NumberField
open scoped TensorProduct
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.RegSS.adj_map {B : Type} [CommRing B] (σ : A →+* A) (τ : B →+* B)
    (f : A →+* B) (hf : ∀ x, f (σ x) = τ (f x)) {J : Matrix n n A} (hJ : IsUnit J.det)
    (a : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj τ (J.map f) (a.map f) = (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a).map f := by sorry
