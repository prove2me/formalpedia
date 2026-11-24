-- Prove2me | Theorems.Thm_GlobalTheory_relIndex_dualSubmodule
-- name    : GlobalTheory.relIndex_dualSubmodule
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:35.83223+00:00
-- url     : https://prove2.me/theorems/e86039c4-00d9-4991-bd02-67b40c15dc94
-- title:
--   Global Theory: rel Index dual Submodule
-- statement:
--   The Global Theory construction uses the rel Index dual Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L96-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L96-L113

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

theorem GlobalTheory.relIndex_dualSubmodule (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    {M N : Submodule ℤ V} [M.IsLattice ℚ] [N.IsLattice ℚ] (h : M ≤ N) :
    (B.dualSubmodule N).toAddSubgroup.relIndex (B.dualSubmodule M).toAddSubgroup =
      M.toAddSubgroup.relIndex N.toAddSubgroup := by sorry
