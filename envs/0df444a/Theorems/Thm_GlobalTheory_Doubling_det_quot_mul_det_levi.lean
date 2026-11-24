-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_det_quot_mul_det_levi
-- name    : GlobalTheory.Doubling.det_quot_mul_det_levi
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:24.41884+00:00
-- url     : https://prove2.me/theorems/9ec627d6-9b53-4e0e-8a43-183569c78e4b
-- title:
--   Doubling: det quot mul det levi
-- statement:
--   The Doubling construction uses the det quot mul det levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L315-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L315-L320

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]

theorem GlobalTheory.Doubling.det_quot_mul_det_levi {σ : A →+* A} {J : Matrix n n A} (hJ : IsUnit J.det) {M : Matrix ι ι A}
    (hM : cT σ M * dblGram e J * M = dblGram e J) (h : KeepsDiag e M) :
    σ (quotMat e M).det * (leviMat e M).det = 1 := by sorry
