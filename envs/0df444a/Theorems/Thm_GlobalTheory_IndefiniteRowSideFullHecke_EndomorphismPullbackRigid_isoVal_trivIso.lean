-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EndomorphismPullbackRigid_isoVal_trivIso
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.isoVal_trivIso
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:16:31.284738+00:00
-- url     : https://prove2.me/theorems/3d6d2dc3-6a5f-45a9-ba85-8dd7c663abe7
-- title:
--   Endomorphism Pullback Rigid: iso Val triv Iso
-- statement:
--   The Endomorphism Pullback Rigid construction uses the iso Val triv Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean#L154-L156

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
omit [IsCommMonObj A]

theorem GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.isoVal_trivIso {T W : Over X} (f : T ⊗ A ⟶ A) (a b : ℤ) (t : W ⟶ T) (v u : W ⟶ A)
    (hu : lift t v ≫ f = u) (i j) (hi) (hj) : isoVal (trivIso f a b) t v u hu i j hi hj = 1 := by sorry
