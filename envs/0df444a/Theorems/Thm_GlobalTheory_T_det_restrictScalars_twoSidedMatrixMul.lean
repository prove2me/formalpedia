-- Prove2me | Theorems.Thm_GlobalTheory_T_det_restrictScalars_twoSidedMatrixMul
-- name    : GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:17.896705+00:00
-- url     : https://prove2.me/theorems/d7af854d-971d-4209-838a-4108d7b5f1dd
-- title:
--   T: det restrict Scalars two Sided Matrix Mul
-- statement:
--   The T construction uses the det restrict Scalars two Sided Matrix Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetRestrictScalarsTwoSidedMatrixMulStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetRestrictScalarsTwoSidedMatrixMulStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetRestrictScalarsTwoSidedMatrixMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetRestrictScalarsTwoSidedMatrixMulStatement
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

theorem GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul : ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) (T : Matrix α ν E →ₗ[F] Matrix α ν E), (∀ x, T x = u * x * a) → LinearMap.det T = Algebra.norm F u.det ^ Fintype.card ν * Algebra.norm F a.det ^ Fintype.card α := by sorry
