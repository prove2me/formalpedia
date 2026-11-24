-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mulVec_mem_stdLattice
-- name    : GroundTheory.Automorphic.mulVec_mem_stdLattice
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:46.252112+00:00
-- url     : https://prove2.me/theorems/fc8e6a49-ad2b-4ff8-9068-ec02c39efc5a
-- title:
--   Automorphic: mul Vec mem std Lattice
-- statement:
--   The Automorphic construction uses the mul Vec mem std Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Lattice.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Lattice.lean#L86-L91

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

theorem GroundTheory.Automorphic.mulVec_mem_stdLattice {O : Subring R} (hO : IsAdapted b O) {M : Matrix ι ι (R ⊗[K] E)}
    (hM : ∀ i j k, (Algebra.TensorProduct.basis R b).repr (M i j) k ∈ O) {x : ι → R ⊗[K] E}
    (hx : x ∈ stdLattice ι R b O) : M *ᵥ x ∈ stdLattice ι R b O := by sorry
