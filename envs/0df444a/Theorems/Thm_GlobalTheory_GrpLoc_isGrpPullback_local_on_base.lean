-- Prove2me | Theorems.Thm_GlobalTheory_GrpLoc_isGrpPullback_local_on_base
-- name    : GlobalTheory.GrpLoc.isGrpPullback_local_on_base
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:35.028731+00:00
-- url     : https://prove2.me/theorems/156ca876-fcd7-4645-b0de-9000b2fb5087
-- title:
--   Grp Loc: is Grp Pullback local on base
-- statement:
--   The Grp Loc construction uses the is Grp Pullback local on base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsGrpPullbackLocalOnBase.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsGrpPullbackLocalOnBase.lean#L85-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsGrpPullbackLocalOnBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.GrpLoc

theorem GlobalTheory.GrpLoc.isGrpPullback_local_on_base : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left), IsIso φ → φ ≫ A'.hom = A.hom → (∀ p : S, ∃ (V : Scheme.{0}) (x : V ⟶ S) (B : Over V) (_ : GrpObj B) (a : B.left ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) → IsGrpPullback A A' (𝟙 S) φ := by sorry
