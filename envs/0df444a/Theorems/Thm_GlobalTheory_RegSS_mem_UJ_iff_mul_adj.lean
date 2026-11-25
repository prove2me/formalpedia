-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_mem_UJ_iff_mul_adj
-- name    : GlobalTheory.RegSS.mem_UJ_iff_mul_adj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:05.031594+00:00
-- url     : https://prove2.me/theorems/39214d38-14fb-41a6-8255-740d5e3daa3f
-- title:
--   Reg SS: mem UJ iff mul adj
-- statement:
--   The Reg SS construction uses the mem UJ iff mul adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L417-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L417-L433

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

theorem GlobalTheory.RegSS.mem_UJ_iff_mul_adj (σ : A →+* A) {J : Matrix n n A}
    (hJ : IsUnit J.det) (g : GL n A) :
    g ∈ _root_.Formalism.UG.UJ σ J ↔ (g : Matrix n n A) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (g : Matrix n n A) = 1 := by sorry
