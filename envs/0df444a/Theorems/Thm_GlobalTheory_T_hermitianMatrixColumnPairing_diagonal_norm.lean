-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianMatrixColumnPairing_diagonal_norm
-- name    : GlobalTheory.T.hermitianMatrixColumnPairing_diagonal_norm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:36:12.337689+00:00
-- url     : https://prove2.me/theorems/3dd90698-6627-46e9-a73e-858b7ad35c99
-- title:
--   T: hermitian Matrix Column Pairing diagonal norm
-- statement:
--   The T construction uses the hermitian Matrix Column Pairing diagonal norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianMatrixColumnPairingDiagonalNormStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianMatrixColumnPairingDiagonalNormStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingDiagonalNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingDiagonalNormStatement
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

theorem GlobalTheory.T.hermitianMatrixColumnPairing_diagonal_norm : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (u : Matrix α α E) (D' : α → F) (a : Matrix ν ν E) (D : ν → F), Q = u * diagonal (fun i => algebraMap F E (D' i)) * (u.map c)ᵀ → ∀ x : Matrix α ν E, 2⁻¹ * pr c Q x (x * (a * diagonal (fun j => algebraMap F E (D j)) * (a.map c)ᵀ)) = ∑ i, ∑ j, (2⁻¹ * D' i * D j) * Algebra.norm F ((uᵀ * x * a) i j) := by sorry
