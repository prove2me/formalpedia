-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_tensorCoordsHomeomorph_apply
-- name    : GroundTheory.Automorphic.tensorCoordsHomeomorph_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:56.145292+00:00
-- url     : https://prove2.me/theorems/40b5c1ba-e950-4e5b-9a1e-db59d473e7f0
-- title:
--   Automorphic: tensor Coords Homeomorph apply
-- statement:
--   The Automorphic construction uses the tensor Coords Homeomorph apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L181-L182

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

theorem GroundTheory.Automorphic.tensorCoordsHomeomorph_apply (z : R ⊗[K] E) (k : κ) :
    tensorCoordsHomeomorph R b z k = (Algebra.TensorProduct.basis R b).repr z k := by sorry
