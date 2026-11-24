-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_unipEquiv_mul
-- name    : GlobalTheory.SmGL.UnipHaar.unipEquiv_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:13:43.460219+00:00
-- url     : https://prove2.me/theorems/5145d74a-3ec5-4005-abb6-202dea9d5c3a
-- title:
--   Unip Haar: unip Equiv mul
-- statement:
--   The Unip Haar construction uses the unip Equiv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L184-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L184-L190

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

theorem GlobalTheory.SmGL.UnipHaar.unipEquiv_mul (u : unipRad R e) (x : Idx e → R) :
    unipEquiv e (u * (unipEquiv e).symm x) =
      unipEquiv e u + (lmat e ((u : GL n R) : Matrix n n R)).mulVec x := by sorry
