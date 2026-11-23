-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- name    : GroundTheory.Automorphic.unitaryPiEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:06.275692+00:00
-- url     : https://prove2.me/theorems/788ffc38-64e0-43c2-a7c5-b41c75b4c155
-- title:
--   Automorphic: unitary Pi Equiv apply
-- statement:
--   The Automorphic construction uses the unitary Pi Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L459-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean#L459-L460

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
variable {H R}
variable {S : Type*} [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]
variable (H)
variable (K R S)
variable {J : Type*} (T : J → Type*) [∀ j, CommRing (T j)] [∀ j, Algebra K (T j)]
  [∀ j, TopologicalSpace (T j)] [∀ j, IsTopologicalRing (T j)]

theorem GroundTheory.Automorphic.unitaryPiEquiv_apply (hH : IsUnit H.det) (g : unitaryPoints K E H (∀ j, T j)) (j : J) :
    unitaryPiEquiv K H T hH g j = unitaryMap K E H (Pi.evalAlgHom K T j) g := by sorry

attribute [defeq] GroundTheory.Automorphic.unitaryPiEquiv_apply
