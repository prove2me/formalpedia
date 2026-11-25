-- Prove2me | Theorems.Thm_GlobalTheory_T_abelianFunctorNilChart_of_nilpotent_chart
-- name    : GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T18:06:35.531131+00:00
-- url     : https://prove2.me/theorems/93822d45-befc-44cd-9eed-14dff3a521d0
-- title:
--   T: abelian Functor Nil Chart of nilpotent chart
-- statement:
--   The T construction uses the abelian Functor Nil Chart of nilpotent chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AbelianFunctorNilChartOfNilpotentChartStatement.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AbelianFunctorNilChartOfNilpotentChartStatement.lean#L20-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AbelianFunctorNilChartOfNilpotentChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AbelianFunctorNilChartOfNilpotentChartStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart : ∀ (R₀ : Type) [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ → ∀ (g : ℕ) (F : Fin g → PS (O : Type) 2 g) (X : Fam G' g), NilChart G' F X → ∃ Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R, BXChart B O F Y ∧ ∀ (f : G' ⟶ G') (α : Fin g → PS (O : Type) 1 g) (A : OEnd B O), Reads X X f α → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.f s x)).left) → ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a]) := by sorry
