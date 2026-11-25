-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_single_one_mem_stdLattice
-- name    : GroundTheory.Automorphic.single_one_mem_stdLattice
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:06.594524+00:00
-- url     : https://prove2.me/theorems/949dbca4-7f48-4745-8106-3e5e869857cf
-- title:
--   Automorphic: single one mem std Lattice
-- statement:
--   The Automorphic construction uses the single one mem std Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Lattice.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Lattice.lean#L76-L84

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
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
open Module Matrix TensorProduct
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {R : Type*} [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable {H b}

theorem GroundTheory.Automorphic.single_one_mem_stdLattice {O : Subring R} (hO : IsAdapted b O) (j : ι) :
    (Pi.single j 1 : ι → R ⊗[K] E) ∈ stdLattice ι R b O := by sorry
