-- Prove2me | Theorems.Thm_GlobalTheory_isLattice_of_fg_dualSubmodule
-- name    : GlobalTheory.isLattice_of_fg_dualSubmodule
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:23.827409+00:00
-- url     : https://prove2.me/theorems/9be222b4-9f41-43eb-818f-75d05898488a
-- title:
--   Global Theory: is Lattice of fg dual Submodule
-- statement:
--   The Global Theory construction uses the is Lattice of fg dual Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L38-L50

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

theorem GlobalTheory.isLattice_of_fg_dualSubmodule (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) (hL : L.FG) (hd : (B.dualSubmodule L).FG) : L.IsLattice ℚ := by sorry
