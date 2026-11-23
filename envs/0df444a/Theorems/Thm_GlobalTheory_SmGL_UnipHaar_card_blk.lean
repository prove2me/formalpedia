-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_card_blk
-- name    : GlobalTheory.SmGL.UnipHaar.card_blk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:52.555132+00:00
-- url     : https://prove2.me/theorems/df237457-ea8e-4488-8ed5-b9504107b41d
-- title:
--   Unip Haar: card blk
-- statement:
--   The Unip Haar construction uses the card blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L134-L138

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
omit [LinearOrder α] [∀ a, DecidableEq (m a)] [DecidableEq n]

theorem GlobalTheory.SmGL.UnipHaar.card_blk (p : α → Prop) [DecidablePred p] :
    Fintype.card {j : n // p (blk e j)} = ∑ b with p b, Fintype.card (m b) := by sorry
