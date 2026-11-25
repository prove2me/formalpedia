-- Prove2me | Theorems.Thm_GlobalTheory_adjAdd
-- name    : GlobalTheory.adjAdd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T16:55:38.593273+00:00
-- url     : https://prove2.me/theorems/01dc3587-9d58-5351-8039-bfc245a0a85a
-- title:
--   Global Theory: adj Add
-- statement:
--   The Global Theory construction uses the adj Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GrpPullbackSquareProductLift.lean#L165-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GrpPullbackSquareProductLift.lean#L165-L213

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GrpPullbackSquareProductLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {σ : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G σ φ)

theorem GlobalTheory.adjAdd (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') {P : LB (G ⊗ G).left} (β : IsBiext G P)
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (sq : IsSquare φ φ₂) (f f' : G' ⟶ G') [IsMonHom f] [IsMonHom f']
    (t : LB.Gen (LB.LinComb P (K := Fin 2) ![(lift (fst G' G' ≫ f) (snd G' G')).left ≫ φ₂,
      (lift (fst G' G') (snd G' G' ≫ f')).left ≫ φ₂] ![1, -1])) (ht : t.IsGen)
    {T : Over S'} (x x' y : T ⟶ G') {z : T.left} {J} (hJ : Good P z J) :
    val β.law1 (adjPair3 gp x x' (y ≫ f')) z J * (val t (lift (x * x') y).left z J *
        val t (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J) =
      val β.law1 (adjPair3 gp (x ≫ f) (x' ≫ f) y) z J * (val t (lift x y).left z J * val t (lift x' y).left z J) ∧
    val β.law2 (adjPair3 gp y (x ≫ f') (x' ≫ f')) z J * (val t (lift y (x * x')).left z J *
        val t (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J) =
      val β.law2 (adjPair3 gp (y ≫ f) x x') z J * (val t (lift y x).left z J * val t (lift y x').left z J) := by sorry
