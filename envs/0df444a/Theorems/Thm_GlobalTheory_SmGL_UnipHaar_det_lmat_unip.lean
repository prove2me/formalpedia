-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_lmat_unip
-- name    : GlobalTheory.SmGL.UnipHaar.det_lmat_unip
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:13:57.272917+00:00
-- url     : https://prove2.me/theorems/03f0148e-e1a9-44c2-a254-c7b78c3af02e
-- title:
--   Unip Haar: det lmat unip
-- statement:
--   The Unip Haar construction uses the det lmat unip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L192-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L192-L194

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

theorem GlobalTheory.SmGL.UnipHaar.det_lmat_unip (u : unipRad R e) : (lmat e ((u : GL n R) : Matrix n n R)).det = 1 := by sorry
