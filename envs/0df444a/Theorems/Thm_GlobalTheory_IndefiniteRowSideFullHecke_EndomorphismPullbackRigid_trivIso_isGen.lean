-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EndomorphismPullbackRigid_trivIso_isGen
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.trivIso_isGen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:55.262487+00:00
-- url     : https://prove2.me/theorems/332779ee-c1b4-429c-b111-fdadca62bf20
-- title:
--   Endomorphism Pullback Rigid: triv Iso is Gen
-- statement:
--   The Endomorphism Pullback Rigid construction uses the triv Iso is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean#L142-L151

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.trivIso_isGen {T : Over X} (f : T ⊗ A ⟶ A) (a b : ℤ) : (trivIso f a b).IsGen := by sorry
