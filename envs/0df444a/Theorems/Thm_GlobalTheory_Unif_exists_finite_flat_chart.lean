-- Prove2me | Theorems.Thm_GlobalTheory_Unif_exists_finite_flat_chart
-- name    : GlobalTheory.Unif.exists_finite_flat_chart
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:50.735039+00:00
-- url     : https://prove2.me/theorems/631aa495-b003-4812-9ae1-5851a8cf5b8a
-- title:
--   Unif: exists finite flat chart
-- statement:
--   The Unif construction uses the exists finite flat chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FinFlatChartOfOpenImmersion.lean#L56-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FinFlatChartOfOpenImmersion.lean#L56-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinFlatChartOfOpenImmersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
open GlobalTheory GlobalTheory.Unif

theorem GlobalTheory.Unif.exists_finite_flat_chart : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f], ∃ (g : ℕ) (W : X.Opens) (V : (Spec (CommRingCat.of (MvPolynomial (Fin g) K))).Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧ IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) = W.ι ≫ f := by sorry
