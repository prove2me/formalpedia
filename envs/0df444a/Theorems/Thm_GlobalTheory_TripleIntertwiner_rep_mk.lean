-- Prove2me | Theorems.Thm_GlobalTheory_TripleIntertwiner_rep_mk
-- name    : GlobalTheory.TripleIntertwiner.rep_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:42.038801+00:00
-- url     : https://prove2.me/theorems/582e5850-75ba-48ea-a2ec-41af17ca6249
-- title:
--   Triple Intertwiner: rep mk
-- statement:
--   The Triple Intertwiner construction uses the rep mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L91-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
variable {V : Type*} [AddCommGroup V]

theorem GlobalTheory.TripleIntertwiner.rep_mk {B A : AddSubgroup V} (a : A) :
    ∃ l, l ∈ A ∧ l ∈ B ∧ rep (QuotientAddGroup.mk a : A ⧸ B.addSubgroupOf A) = a + l := by sorry
