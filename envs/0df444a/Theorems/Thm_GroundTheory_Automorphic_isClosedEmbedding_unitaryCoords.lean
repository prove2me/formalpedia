-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isClosedEmbedding_unitaryCoords
-- name    : GroundTheory.Automorphic.isClosedEmbedding_unitaryCoords
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:33.507406+00:00
-- url     : https://prove2.me/theorems/cf507aec-e96e-4b40-9a19-36252e5250c0
-- title:
--   Automorphic: is Closed Embedding unitary Coords
-- statement:
--   The Automorphic construction uses the is Closed Embedding unitary Coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L284-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L284-L286

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

theorem GroundTheory.Automorphic.isClosedEmbedding_unitaryCoords (hH : IsUnit H.det) [T2Space R] :
    IsClosedEmbedding (unitaryCoords H R b) := by sorry
