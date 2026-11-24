-- Prove2me | Theorems.Thm_GlobalTheory_KSp_exists_gl_diagonal_hermitian
-- name    : GlobalTheory.KSp.exists_gl_diagonal_hermitian
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:34.985806+00:00
-- url     : https://prove2.me/theorems/2799144a-008f-4eac-a846-7761e9a66b5d
-- title:
--   KSp: exists gl diagonal hermitian
-- statement:
--   The KSp construction uses the exists gl diagonal hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGLDiagonalCongruentHermitian.lean#L10-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGLDiagonalCongruentHermitian.lean#L10-L49

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGLDiagonalCongruentHermitian
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
open GlobalTheory GlobalTheory.KSp

theorem GlobalTheory.KSp.exists_gl_diagonal_hermitian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by sorry
