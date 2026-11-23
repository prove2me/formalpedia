-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_sum_idx
-- name    : GlobalTheory.SmGL.UnipHaar.sum_idx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:49.894509+00:00
-- url     : https://prove2.me/theorems/470184b4-cf05-42c2-af22-30dbdef4eafc
-- title:
--   Unip Haar: sum idx
-- statement:
--   The Unip Haar construction uses the sum idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L59-L67

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
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [DecidableEq n]

theorem GlobalTheory.SmGL.UnipHaar.sum_idx (f : n → n → R) (x : Idx e → R) :
    ∑ q : Idx e, f q.1.1 q.1.2 * x q = ∑ i, ∑ j, f i j * mat e x i j := by sorry
