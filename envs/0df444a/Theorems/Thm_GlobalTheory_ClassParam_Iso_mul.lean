-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_Iso_mul
-- name    : GlobalTheory.ClassParam.Iso.mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:29.820688+00:00
-- url     : https://prove2.me/theorems/5bf1e87c-78d3-42e6-bc89-c17be1b05f94
-- title:
--   Iso: mul
-- statement:
--   The Iso construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L280-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L280-L287

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

theorem GlobalTheory.ClassParam.Iso.mul {x : B} {φ : B ≃ₗ[A] (Fin r → A)} (h : Iso σ τ J x φ) (z : Bˣ) :
    Iso σ τ J (x * (z * τ z)) (mulUnit A z ≪≫ₗ φ) := by sorry
