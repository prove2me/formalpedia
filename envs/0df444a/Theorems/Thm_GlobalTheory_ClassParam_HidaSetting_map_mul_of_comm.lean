-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_map_mul_of_comm
-- name    : GlobalTheory.ClassParam.HidaSetting.map_mul_of_comm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:13:22.40692+00:00
-- url     : https://prove2.me/theorems/f81634ed-3274-45d6-bb4d-18632c60da7b
-- title:
--   Hida Setting: map mul of comm
-- statement:
--   The Hida Setting construction uses the map mul of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L330-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L330-L338

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

theorem GlobalTheory.ClassParam.HidaSetting.map_mul_of_comm (S : HidaSetting σ τ α b) (ψ : B →ₗ[A] B)
    (h : ∀ y, ψ (α * y) = α * ψ y) (y : B) : ψ y = ψ 1 * y := by sorry
