-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_ent_mat_mul
-- name    : GlobalTheory.SmGL.UnipHaar.ent_mat_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:38.40716+00:00
-- url     : https://prove2.me/theorems/3a6a6435-4a7f-4ab8-b1c1-6aaf0a207689
-- title:
--   Unip Haar: ent mat mul
-- statement:
--   The Unip Haar construction uses the ent mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L77-L82

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
variable (e : (Σ a, m a) ≃ n)
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem GlobalTheory.SmGL.UnipHaar.ent_mat_mul (B : Matrix n n R) (x : Idx e → R) :
    ent e (mat e x * B) = (rmat e B).mulVec x := by sorry
