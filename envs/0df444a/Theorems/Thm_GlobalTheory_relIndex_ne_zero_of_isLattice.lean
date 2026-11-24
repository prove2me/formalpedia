-- Prove2me | Theorems.Thm_GlobalTheory_relIndex_ne_zero_of_isLattice
-- name    : GlobalTheory.relIndex_ne_zero_of_isLattice
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:13.51747+00:00
-- url     : https://prove2.me/theorems/85090976-ca7d-4b83-a7e2-c7c748b6e0f6
-- title:
--   Global Theory: rel Index ne zero of is Lattice
-- statement:
--   The Global Theory construction uses the rel Index ne zero of is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L87-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable [FiniteDimensional ℚ V]

theorem GlobalTheory.relIndex_ne_zero_of_isLattice {M N : Submodule ℤ V} [M.IsLattice ℚ] [N.IsLattice ℚ]
    (h : M ≤ N) : M.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by sorry
