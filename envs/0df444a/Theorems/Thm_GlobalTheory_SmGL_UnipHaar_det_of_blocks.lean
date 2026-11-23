-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_of_blocks
-- name    : GlobalTheory.SmGL.UnipHaar.det_of_blocks
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:00.0448+00:00
-- url     : https://prove2.me/theorems/f9c2c3b2-1427-4810-bfd5-07d6669497a9
-- title:
--   Unip Haar: det of blocks
-- statement:
--   The Unip Haar construction uses the det of blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L17-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem GlobalTheory.SmGL.UnipHaar.det_of_blocks {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I R) (b : I → α)
    (hM : M.BlockTriangular b) (T : α → Type) [∀ a, Fintype (T a)] [∀ a, DecidableEq (T a)]
    (A : ∀ a, Matrix (m a) (m a) R) (φ : ∀ a, m a × T a ≃ {p // b p = a})
    (h : ∀ a x y, M (φ a x) (φ a y) = if x.2 = y.2 then A a x.1 y.1 else 0) :
    M.det = ∏ a, (A a).det ^ Fintype.card (T a) := by sorry
