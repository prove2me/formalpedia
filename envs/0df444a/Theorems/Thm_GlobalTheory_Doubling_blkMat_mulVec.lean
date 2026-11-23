-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_blkMat_mulVec
-- name    : GlobalTheory.Doubling.blkMat_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:36.60245+00:00
-- url     : https://prove2.me/theorems/1b9baa3f-0eb0-412d-933b-91d3629fcb9e
-- title:
--   Doubling: blk Mat mul Vec
-- statement:
--   The Doubling construction uses the blk Mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L70-L72

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : m ⊕ n ≃ ι)
variable [Fintype m] [Fintype n] [Fintype ι]

theorem GlobalTheory.Doubling.blkMat_mulVec (x : Matrix m m A) (y : Matrix n n A) (u : m → A) (v : n → A) :
    blkMat e x y *ᵥ pairVec e u v = pairVec e (x *ᵥ u) (y *ᵥ v) := by sorry
