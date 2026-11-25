-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_openAddSubgroup_invariant_of_locallyConstant
-- name    : GlobalTheory.T.exists_openAddSubgroup_invariant_of_locallyConstant
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:15.789479+00:00
-- url     : https://prove2.me/theorems/cae49560-60cc-51a7-b1ba-6b644b6b7ecd
-- title:
--   T: exists open Add Subgroup invariant of locally Constant
-- statement:
--   The T construction uses the exists open Add Subgroup invariant of locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyConstantCompactSupportInvariantOpenAddSubStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyConstantCompactSupportInvariantOpenAddSubStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyConstantCompactSupportInvariantOpenAddSub
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyConstantCompactSupportInvariantOpenAddSubStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_openAddSubgroup_invariant_of_locallyConstant : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [NonarchimedeanAddGroup X] (g : X → ℂ), IsLocallyConstant g → HasCompactSupport g → ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z := by sorry
