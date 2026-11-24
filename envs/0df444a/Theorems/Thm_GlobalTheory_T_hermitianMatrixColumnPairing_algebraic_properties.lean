-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianMatrixColumnPairing_algebraic_properties
-- name    : GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:34:52.446564+00:00
-- url     : https://prove2.me/theorems/9318a52a-d29a-43fb-85c8-53d456fdb554
-- title:
--   T: hermitian Matrix Column Pairing algebraic properties
-- statement:
--   The T construction uses the hermitian Matrix Column Pairing algebraic properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianMatrixColumnPairingAlgebraicPropertiesStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianMatrixColumnPairingAlgebraicPropertiesStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicPropertiesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F, (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧ (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧ ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by sorry
