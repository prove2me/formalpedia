-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_isUnit_det_gram
-- name    : GlobalTheory.ClassParam.HidaSetting.isUnit_det_gram
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:13:17.506687+00:00
-- url     : https://prove2.me/theorems/fd44c685-05e4-4979-9a63-340b7944c472
-- title:
--   Hida Setting: is Unit det gram
-- statement:
--   The Hida Setting construction uses the is Unit det gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L500-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L500-L519

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

theorem GlobalTheory.ClassParam.HidaSetting.isUnit_det_gram (S : HidaSetting σ τ α b) {x : B} (hx : IsUnit x) :
    IsUnit (gram τ x b).det := by sorry
