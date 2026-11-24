-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_repr_mul_mem
-- name    : GroundTheory.Automorphic.repr_mul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:41.702043+00:00
-- url     : https://prove2.me/theorems/77aa3141-7f30-4866-a71a-93e03cdfc4ee
-- title:
--   Automorphic: repr mul mem
-- statement:
--   The Automorphic construction uses the repr mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Lattice.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Lattice.lean#L68-L74

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

theorem GroundTheory.Automorphic.repr_mul_mem {O : Subring R} (hO : IsAdapted b O) {z w : R ⊗[K] E}
    (hz : ∀ k, (Algebra.TensorProduct.basis R b).repr z k ∈ O)
    (hw : ∀ k, (Algebra.TensorProduct.basis R b).repr w k ∈ O) (m : κ) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m ∈ O := by sorry
