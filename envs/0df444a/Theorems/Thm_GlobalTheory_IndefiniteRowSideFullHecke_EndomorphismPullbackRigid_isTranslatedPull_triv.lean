-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EndomorphismPullbackRigid_isTranslatedPull_triv
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.isTranslatedPull_triv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:33.082549+00:00
-- url     : https://prove2.me/theorems/37090829-4cfe-4f24-b5c6-deec9cf8ca61
-- title:
--   Endomorphism Pullback Rigid: is Translated Pull triv
-- statement:
--   The Endomorphism Pullback Rigid construction uses the is Translated Pull triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean#L166-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean#L166-L174

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.isTranslatedPull_triv (φ : A ⟶ A) [IsMonHom φ] {N : ℕ} (hN : Odd N) {T : Over X}
    (b : T ⟶ A) (hb : b ^ N = 1) :
    IsTranslatedPull (trivRig A) φ N b (trivOne 1 T) (trivOne N T) := by sorry
