-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_blkGL_mem_stabGL
-- name    : GlobalTheory.Doubling.blkGL_mem_stabGL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:11.418213+00:00
-- url     : https://prove2.me/theorems/a228ed5a-a187-4cf9-93bb-669d99271626
-- title:
--   Doubling: blk GL mem stab GL
-- statement:
--   The Doubling construction uses the blk GL mem stab GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L129-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L129-L136

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
omit [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]

theorem GlobalTheory.Doubling.blkGL_mem_stabGL [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]
    {O : Type} [CommRing O] [Algebra O A] {L : Submodule O (m → A)} {L' : Submodule O (n → A)} {x : GL m A} {y : GL n A} :
    blkGL e (x, y) ∈ stabGL (sumLat e L L') ↔ x ∈ stabGL L ∧ y ∈ stabGL L' := by sorry
