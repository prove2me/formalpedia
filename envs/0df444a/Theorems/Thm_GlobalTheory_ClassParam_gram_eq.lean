-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_gram_eq
-- name    : GlobalTheory.ClassParam.gram_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:43.761475+00:00
-- url     : https://prove2.me/theorems/a71cfaaa-0980-4997-852d-482b6f469cc9
-- title:
--   Class Param: gram eq
-- statement:
--   The Class Param construction uses the gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L467-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L467-L473

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

theorem GlobalTheory.ClassParam.gram_eq (x : B) (e : Module.Basis (Fin r) A B) :
    gram τ x e = (Algebra.leftMulMatrix e x)ᵀ * gram τ 1 e := by sorry
