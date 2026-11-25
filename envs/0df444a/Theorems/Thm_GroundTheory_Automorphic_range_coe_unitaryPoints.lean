-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_range_coe_unitaryPoints
-- name    : GroundTheory.Automorphic.range_coe_unitaryPoints
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:52.017491+00:00
-- url     : https://prove2.me/theorems/3345e6cf-9775-42d9-92a5-f03e07795237
-- title:
--   Automorphic: range coe unitary Points
-- statement:
--   The Automorphic construction uses the range coe unitary Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L263-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L263-L273

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
attribute [local instance] tensorTopology finite_of_isQuadraticExtension
variable (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
attribute [local instance] isModuleTopology_tensor
attribute [local instance] isTopologicalRing_tensor
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable {H R}
variable (H R)

theorem GroundTheory.Automorphic.range_coe_unitaryPoints (hH : IsUnit H.det) :
    Set.range (fun g : unitaryPoints K E H R => (unitaryMat g)) =
      {M | (M.map (conjBase K E R))ᵀ * baseMatrix K H R * M = baseMatrix K H R} := by sorry
