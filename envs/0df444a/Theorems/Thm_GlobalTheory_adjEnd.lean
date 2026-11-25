-- Prove2me | Theorems.Thm_GlobalTheory_adjEnd
-- name    : GlobalTheory.adjEnd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:42.676746+00:00
-- url     : https://prove2.me/theorems/40171dd3-2c43-5678-a402-f785daa274ac
-- title:
--   Global Theory: adj End
-- statement:
--   The Global Theory construction uses the adj End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GrpPullbackSquareProductLift.lean#L242-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GrpPullbackSquareProductLift.lean#L242-L276

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
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.adjEnd {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] (B : BX R₀)
    (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)) (hb : ∀ R, Function.Bijective (e R))
    (hm : ∀ R x y, e R (x + y) = e R x * e R y)
    (hn : ∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)
    (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] (φ : G'.left ⟶ G.left)
    (gp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ)
    (f : G' ⟶ G') [IsMonHom f] : ∃ a : OEnd B O, ∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (a.f s x)).left := by sorry
