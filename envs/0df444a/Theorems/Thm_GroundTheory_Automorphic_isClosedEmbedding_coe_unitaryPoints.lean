-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isClosedEmbedding_coe_unitaryPoints
-- name    : GroundTheory.Automorphic.isClosedEmbedding_coe_unitaryPoints
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:47.154865+00:00
-- url     : https://prove2.me/theorems/0ae4a886-bfc1-497c-b6a1-e6283e994e50
-- title:
--   Automorphic: is Closed Embedding coe unitary Points
-- statement:
--   The Automorphic construction uses the is Closed Embedding coe unitary Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L275-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L275-L282

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

theorem GroundTheory.Automorphic.isClosedEmbedding_coe_unitaryPoints (hH : IsUnit H.det) [T2Space R] :
    IsClosedEmbedding (fun g : unitaryPoints K E H R => (unitaryMat g)) := by sorry
