-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_det_gram_fixed
-- name    : GlobalTheory.ClassParam.HidaSetting.det_gram_fixed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:13:40.288838+00:00
-- url     : https://prove2.me/theorems/1d294b5b-a080-4645-aa86-27fd3dea6b99
-- title:
--   Hida Setting: det gram fixed
-- statement:
--   The Hida Setting construction uses the det gram fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L521-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L521-L528

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

theorem GlobalTheory.ClassParam.HidaSetting.det_gram_fixed (S : HidaSetting σ τ α b) {x : B} (hx : τ x = x)
    (e : Module.Basis (Fin r) A B) : σ (gram τ x e).det = (gram τ x e).det := by sorry
