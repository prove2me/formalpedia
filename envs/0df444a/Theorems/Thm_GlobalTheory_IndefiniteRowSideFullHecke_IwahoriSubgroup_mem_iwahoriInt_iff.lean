-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_IwahoriSubgroup_mem_iwahoriInt_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.mem_iwahoriInt_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:47:19.065927+00:00
-- url     : https://prove2.me/theorems/8aec4cc8-0f33-53a2-bdb3-9b55c07169c8
-- title:
--   Iwahori Subgroup: mem iwahori Int iff
-- statement:
--   The Iwahori Subgroup construction uses the mem iwahori Int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/IwahoriSubgroup.lean#L64-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/IwahoriSubgroup.lean#L64-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_IwahoriSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup

theorem GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.mem_iwahoriInt_iff (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))] (r : ℕ)
    (g : GL (Fin r) (Int F)) :
    g ∈ iwahoriInt F r ↔ ∀ i j : Fin r, j < i →
      Valued.v (((g : Matrix (Fin r) (Fin r) (Int F)) i j : Int F) : F)
        < (1 : WithZero (Multiplicative ℤ)) := by sorry
