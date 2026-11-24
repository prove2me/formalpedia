-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_latticeStabilizer_iff
-- name    : GroundTheory.Automorphic.mem_latticeStabilizer_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:20.806307+00:00
-- url     : https://prove2.me/theorems/03a85afb-ba3c-4513-b1db-f1ff3b4e02a8
-- title:
--   Automorphic: mem lattice Stabilizer iff
-- statement:
--   The Automorphic construction uses the mem lattice Stabilizer iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Lattice.lean#L93-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Lattice.lean#L93-L106

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

theorem GroundTheory.Automorphic.mem_latticeStabilizer_iff {O : Subring R} (hO : IsAdapted b O)
    (g : unitaryPoints K E H R) :
    g ∈ latticeStabilizer H R b O ↔
      (∀ p, unitaryCoords H R b g p ∈ O) ∧ ∀ p, unitaryCoords H R b g⁻¹ p ∈ O := by sorry
