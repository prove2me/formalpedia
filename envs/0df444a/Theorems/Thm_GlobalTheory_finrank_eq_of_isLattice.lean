-- Prove2me | Theorems.Thm_GlobalTheory_finrank_eq_of_isLattice
-- name    : GlobalTheory.finrank_eq_of_isLattice
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:47:24.029833+00:00
-- url     : https://prove2.me/theorems/381e140f-fe60-4907-9e35-809d0f4ffac1
-- title:
--   Global Theory: finrank eq of is Lattice
-- statement:
--   The Global Theory construction uses the finrank eq of is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L65-L68

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

theorem GlobalTheory.finrank_eq_of_isLattice (L : Submodule ℤ V) [L.IsLattice ℚ] :
    finrank ℤ L = finrank ℚ V := by sorry
