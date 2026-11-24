-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EndomorphismPullbackRigid_rigVal_trivRig
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.rigVal_trivRig
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:57.91371+00:00
-- url     : https://prove2.me/theorems/7ad4d90c-1009-46b3-8467-42f386dc1465
-- title:
--   Endomorphism Pullback Rigid: rig Val triv Rig
-- statement:
--   The Endomorphism Pullback Rigid construction uses the rig Val triv Rig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean#L163-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean#L163-L164

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_EndomorphismPullbackRigid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} {A : Over X}
variable [GrpObj A] [IsCommMonObj A]

theorem GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.rigVal_trivRig (W : Over X) (i) (hi) : rigVal (trivRig A) W i hi = 1 := by sorry
