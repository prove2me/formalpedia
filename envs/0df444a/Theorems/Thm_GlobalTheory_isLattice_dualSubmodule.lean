-- Prove2me | Theorems.Thm_GlobalTheory_isLattice_dualSubmodule
-- name    : GlobalTheory.isLattice_dualSubmodule
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:13.166271+00:00
-- url     : https://prove2.me/theorems/b6245629-84d1-4925-8975-aaa1ef9192c2
-- title:
--   Global Theory: is Lattice dual Submodule
-- statement:
--   The Global Theory construction uses the is Lattice dual Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L70-L75

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

theorem GlobalTheory.isLattice_dualSubmodule (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [L.IsLattice ℚ] : (B.dualSubmodule L).IsLattice ℚ := by sorry
