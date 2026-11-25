-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_quot_mk_eq_iff
-- name    : GlobalTheory.FinWeil.quot_mk_eq_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:04:52.274872+00:00
-- url     : https://prove2.me/theorems/833883c2-a053-4289-b1f1-e0db1367775a
-- title:
--   Fin Weil: quot mk eq iff
-- statement:
--   The Fin Weil construction uses the quot mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumOpTransversal.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumOpTransversal.lean#L14-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.FinWeil.quot_mk_eq_iff (A B : Submodule R X) (x y : B.toAddSubgroup) :
    (QuotientAddGroup.mk x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = QuotientAddGroup.mk y ↔
      (y : X) - x ∈ A := by sorry
