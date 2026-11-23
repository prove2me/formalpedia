-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_span_eq_of_isLattice
-- name    : GlobalTheory.exists_basis_span_eq_of_isLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:57.294648+00:00
-- url     : https://prove2.me/theorems/56e1afe5-0c72-4a45-94c8-695a69760622
-- title:
--   Global Theory: exists basis span eq of is Lattice
-- statement:
--   The Global Theory construction uses the exists basis span eq of is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L52-L63

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

theorem GlobalTheory.exists_basis_span_eq_of_isLattice (L : Submodule ℤ V) [L.IsLattice ℚ] :
    ∃ b : Basis (Fin (finrank ℚ V)) ℚ V, L = Submodule.span ℤ (Set.range b) := by sorry
