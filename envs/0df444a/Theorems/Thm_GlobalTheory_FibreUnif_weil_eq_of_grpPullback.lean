-- Prove2me | Theorems.Thm_GlobalTheory_FibreUnif_weil_eq_of_grpPullback
-- name    : GlobalTheory.FibreUnif.weil_eq_of_grpPullback
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:58.710846+00:00
-- url     : https://prove2.me/theorems/842aa3fc-88ea-498e-b1a6-f979c38dca77
-- title:
--   Fibre Unif: weil eq of grp Pullback
-- statement:
--   The Fibre Unif construction uses the weil eq of grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/FamilyUniformisationFibreTheta.lean#L102-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/FamilyUniformisationFibreTheta.lean#L102-L129

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_FamilyUniformisationFibreTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.FibreUnif

theorem GlobalTheory.FibreUnif.weil_eq_of_grpPullback {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {L₀ : LB G.left} {L : LB A.left}
    (hL₀ : L₀.IsLB) (hL : L.IsLB) (w : LB.Iso L (L₀.pull φ)) (hw : w.IsGen) {Z : Scheme.{0}} [Subsingleton Z]
    {t : Z ⟶ S} {t' : Z ⟶ S'} (ht : t = t' ≫ f) (k : ℤ) (x y : Over.mk t' ⟶ A) (x₀ y₀ : Over.mk t ⟶ G)
    (ex : x₀.left = x.left ≫ φ) (ey : y₀.left = y.left ≫ φ) (c c₀ : Γ(Z, ⊤)ˣ)
    (h : Out.WeilIs A L k x y c) (h₀ : Out.WeilIs G L₀ k x₀ y₀ c₀) : c = c₀ := by sorry
