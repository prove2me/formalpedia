-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_lmat
-- name    : GlobalTheory.SmGL.UnipHaar.det_lmat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:40.247131+00:00
-- url     : https://prove2.me/theorems/229ff8a3-d9ff-44fd-bf24-3ed86534ab29
-- title:
--   Unip Haar: det lmat
-- statement:
--   The Unip Haar construction uses the det lmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L158-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L158-L167

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

theorem GlobalTheory.SmGL.UnipHaar.det_lmat {A : Matrix n n R} (hA : A.BlockTriangular (blk e)) (D : ∀ a, Matrix (m a) (m a) R)
    (hD : ∀ a i j, A (e ⟨a, i⟩) (e ⟨a, j⟩) = D a i j) :
    (lmat e A).det = ∏ a, (D a).det ^ ∑ b with a < b, Fintype.card (m b) := by sorry
