-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_gram_change
-- name    : GlobalTheory.ClassParam.HidaSetting.gram_change
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:13:13.210804+00:00
-- url     : https://prove2.me/theorems/b17b1ea3-b404-42d5-8eaf-802cba70b5ee
-- title:
--   Hida Setting: gram change
-- statement:
--   The Hida Setting construction uses the gram change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L479-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L479-L490

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

theorem GlobalTheory.ClassParam.HidaSetting.gram_change (S : HidaSetting σ τ α b) (x : B) (e e' : Module.Basis (Fin r) A B) :
    gram τ x e' = (e.toMatrix e')ᵀ * gram τ x e * (e.toMatrix e').map σ := by sorry
