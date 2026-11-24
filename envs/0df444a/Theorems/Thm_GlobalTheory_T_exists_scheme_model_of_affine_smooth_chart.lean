-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_scheme_model_of_affine_smooth_chart
-- name    : GlobalTheory.T.exists_scheme_model_of_affine_smooth_chart
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:38:39.719519+00:00
-- url     : https://prove2.me/theorems/45231e98-57d8-48b5-8330-1d8686205c31
-- title:
--   T: exists scheme model of affine smooth chart
-- statement:
--   The T construction uses the exists scheme model of affine smooth chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSchemeModelOfAffineSmoothChartStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSchemeModelOfAffineSmoothChartStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_scheme_model_of_affine_smooth_chart : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)), Smooth A.hom → IsSeparated A.hom → QuasiCompact A.hom → ∀ (C : Type) [CommRing C] [Algebra R C], Algebra.Smooth R C → ∀ u : Sp (TensorProduct R K C) ⟶ A.left, IsOpenImmersion u → u ≫ A.hom = spMap (algebraMap K (TensorProduct R K C)) → ∃ (M : Model R A) (g : Sp C ⟶ M.Y.left), IsOpenImmersion g ∧ g ≫ M.Y.hom = spMap (algebraMap R C) ∧ spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom ≫ g = u ≫ M.j ∧ M.sp ⊆ Set.range g := by sorry
