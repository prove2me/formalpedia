-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_unitaryCoords_apply
-- name    : GroundTheory.Automorphic.unitaryCoords_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:12.183573+00:00
-- url     : https://prove2.me/theorems/bd976adc-45c1-467d-b85f-9a9e16b963f7
-- title:
--   Automorphic: unitary Coords apply
-- statement:
--   The Automorphic construction uses the unitary Coords apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L53-L55

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
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
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem GroundTheory.Automorphic.unitaryCoords_apply (g : unitaryPoints K E H R) (i j : ι) (k : κ) :
    unitaryCoords H R b g (i, j, k) =
      (Algebra.TensorProduct.basis R b).repr (unitaryMat g i j) k := by sorry
