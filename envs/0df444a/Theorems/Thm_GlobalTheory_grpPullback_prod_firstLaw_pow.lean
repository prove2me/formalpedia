-- Prove2me | Theorems.Thm_GlobalTheory_grpPullback_prod_firstLaw_pow
-- name    : GlobalTheory.grpPullback_prod_firstLaw_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:09:00.021327+00:00
-- url     : https://prove2.me/theorems/77aa29ae-1c6b-45f6-a7ed-5b632755994a
-- title:
--   Global Theory: grp Pullback prod first Law pow
-- statement:
--   The Global Theory construction uses the grp Pullback prod first Law pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GrpPullbackSquareProductLift.lean#L87-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GrpPullbackSquareProductLift.lean#L87-L102

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
omit [IsCommMonObj G']

theorem GlobalTheory.grpPullback_prod_firstLaw_pow {T : Over S'} (a b c : T ⟶ G') {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ i, h (adjPair3 gp a b c ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) i) ^ lawε i =
      h (adjPair2 gp (a * b) c) * (h (adjPair2 gp a c))⁻¹ * (h (adjPair2 gp b c))⁻¹ := by sorry
