-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EndomorphismPullbackRigid_secVal_trivOne
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.secVal_trivOne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:52.04705+00:00
-- url     : https://prove2.me/theorems/92ce247f-57ab-46e1-8227-17af1862448f
-- title:
--   Endomorphism Pullback Rigid: sec Val triv One
-- statement:
--   The Endomorphism Pullback Rigid construction uses the sec Val triv One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean#L159-L161

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.secVal_trivOne {T W : Over X} (k : ℤ) (t : W ⟶ T) (v : W ⟶ A) (i) (hi) :
    secVal (trivOne k T) t v i hi = 1 := by sorry
