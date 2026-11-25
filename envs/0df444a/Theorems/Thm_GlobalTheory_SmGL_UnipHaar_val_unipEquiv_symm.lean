-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_val_unipEquiv_symm
-- name    : GlobalTheory.SmGL.UnipHaar.val_unipEquiv_symm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:15.125356+00:00
-- url     : https://prove2.me/theorems/1db1c9af-6bae-4e32-8eb7-38a5c76b9c14
-- title:
--   Unip Haar: val unip Equiv symm
-- statement:
--   The Unip Haar construction uses the val unip Equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L130-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L130-L131

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

theorem GlobalTheory.SmGL.UnipHaar.val_unipEquiv_symm (x : Idx e → R) :
    ((((unipEquiv e).symm x : unipRad R e) : GL n R) : Matrix n n R) = 1 + mat e x := by sorry
