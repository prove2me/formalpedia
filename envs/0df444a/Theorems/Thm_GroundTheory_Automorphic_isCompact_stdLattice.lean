-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isCompact_stdLattice
-- name    : GroundTheory.Automorphic.isCompact_stdLattice
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:12.940536+00:00
-- url     : https://prove2.me/theorems/e32084fb-5dad-5e7e-96a1-c38f7859f428
-- title:
--   Automorphic: is Compact std Lattice
-- statement:
--   The Automorphic construction uses the is Compact std Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/LatticeCompact.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/LatticeCompact.lean#L38-L42

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_LatticeCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct Topology
noncomputable section
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem GroundTheory.Automorphic.isCompact_stdLattice {O : Subring R} (hO : IsCompact (O : Set R)) :
    IsCompact (stdLattice ι R b O) := by sorry
