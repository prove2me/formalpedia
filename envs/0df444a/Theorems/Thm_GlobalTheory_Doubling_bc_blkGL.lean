-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_bc_blkGL
-- name    : GlobalTheory.Doubling.bc_blkGL
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:09.583998+00:00
-- url     : https://prove2.me/theorems/b6b0e17d-cf72-4695-ac36-ade55b9923ad
-- title:
--   Doubling: bc blk GL
-- statement:
--   The Doubling construction uses the bc blk GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L94-L95

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
variable [DecidableEq m] [DecidableEq n] [DecidableEq ι]

theorem GlobalTheory.Doubling.bc_blkGL (f : A →+* B) (x : GL m A) (y : GL n A) : bc f (blkGL e (x, y)) = blkGL e (bc f x, bc f y) := by sorry
