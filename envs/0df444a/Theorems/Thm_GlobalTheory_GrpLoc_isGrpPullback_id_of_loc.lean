-- Prove2me | Theorems.Thm_GlobalTheory_GrpLoc_isGrpPullback_id_of_loc
-- name    : GlobalTheory.GrpLoc.isGrpPullback_id_of_loc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:59:34.76451+00:00
-- url     : https://prove2.me/theorems/0b842c10-9da3-4294-b348-765f74e724fc
-- title:
--   Grp Loc: is Grp Pullback id of loc
-- statement:
--   The Grp Loc construction uses the is Grp Pullback id of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsGrpPullbackLocalOnBase.lean#L41-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsGrpPullbackLocalOnBase.lean#L41-L83

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

theorem GlobalTheory.GrpLoc.isGrpPullback_id_of_loc {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left) [IsIso φ]
    (w : φ ≫ A'.hom = A.hom)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (B : Over W) (_ : GrpObj B) (a : B.left ⟶ A.left),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) :
    IsGrpPullback A A' (𝟙 S) φ := by sorry
