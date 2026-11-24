-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_isConj_of_iso
-- name    : GlobalTheory.ClassParam.isConj_of_iso
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:13:13.514502+00:00
-- url     : https://prove2.me/theorems/07ff04fd-ef68-46ed-b40f-c77118bd20c5
-- title:
--   Class Param: is Conj of iso
-- statement:
--   The Class Param construction uses the is Conj of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L310-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L310-L328

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}

theorem GlobalTheory.ClassParam.isConj_of_iso {x : B} {φ φ' : B ≃ₗ[A] (Fin r → A)} (h : Iso σ τ J x φ)
    (h' : Iso σ τ J x φ') {g g' : UJ σ J}
    (hg : Intw α ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ)
    (hg' : Intw α ((g' : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ') : IsConj g g' := by sorry
