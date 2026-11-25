-- Prove2me | Theorems.Thm_GlobalTheory_SmoothLocusBaseChange_lift_mul_hom_pullback_fst
-- name    : GlobalTheory.SmoothLocusBaseChange.lift_mul_hom_pullback_fst
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:37.429195+00:00
-- url     : https://prove2.me/theorems/b60355bb-882f-58f5-84e6-9d97c174affb
-- title:
--   Smooth Locus Base Change: lift mul hom pullback fst
-- statement:
--   The Smooth Locus Base Change construction uses the lift mul hom pullback fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LiftMulHomPullbackFst.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LiftMulHomPullbackFst.lean#L39-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LiftMulHomPullbackFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SmoothLocusBaseChange

theorem GlobalTheory.SmoothLocusBaseChange.lift_mul_hom_pullback_fst {S S' : Scheme.{0}} (φ : S' ⟶ S) (G : Over S) [GrpObj G]
    {E : Over S'} [MonObj E] (q : E ⟶ (Over.pullback φ).obj G) [IsMonHom q]
    {Z : Over S'} (x y : Z ⟶ E) {Z₀ : Over S} (i : Z₀.left ⟶ Z.left)
    (a b : Z₀ ⟶ G) (ha : a.left = i ≫ x.left ≫ q.left ≫ pullback.fst _ _)
    (hb : b.left = i ≫ y.left ≫ q.left ≫ pullback.fst _ _) :
    (lift a b ≫ μ[G]).left =
      i ≫ (lift x y ≫ μ[E]).left ≫ q.left ≫ pullback.fst _ _ := by sorry
