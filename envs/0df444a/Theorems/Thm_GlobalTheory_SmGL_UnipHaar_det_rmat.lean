-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_rmat
-- name    : GlobalTheory.SmGL.UnipHaar.det_rmat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:14:31.603833+00:00
-- url     : https://prove2.me/theorems/bebc9a28-e8fc-480e-a223-ffede45e0d55
-- title:
--   Unip Haar: det rmat
-- statement:
--   The Unip Haar construction uses the det rmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L169-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L169-L182

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

theorem GlobalTheory.SmGL.UnipHaar.det_rmat (g : Levi R m) :
    (rmat e (leviEmb R e g : Matrix n n R)).det =
      ∏ a, (g a : Matrix (m a) (m a) R).det ^ ∑ b with b < a, Fintype.card (m b) := by sorry
