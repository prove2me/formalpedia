-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_keepsDiag_blkMat
-- name    : GlobalTheory.Doubling.keepsDiag_blkMat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:11.628394+00:00
-- url     : https://prove2.me/theorems/46afbea2-dd20-400d-8007-0926e4c2a368
-- title:
--   Doubling: keeps Diag blk Mat
-- statement:
--   The Doubling construction uses the keeps Diag blk Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L199-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L199-L200

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
variable (e : n ⊕ n ≃ ι)

theorem GlobalTheory.Doubling.keepsDiag_blkMat {x y : Matrix n n A} : KeepsDiag e (blkMat e x y) ↔ y = x := by sorry
