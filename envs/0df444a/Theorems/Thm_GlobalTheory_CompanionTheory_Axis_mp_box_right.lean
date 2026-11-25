-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Axis_mp_box_right
-- name    : GlobalTheory.CompanionTheory.Axis.mp_box_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:56:13.463835+00:00
-- url     : https://prove2.me/theorems/21efe050-d64e-415b-8e7c-e27dc22a4aeb
-- title:
--   Axis: mp box right
-- statement:
--   The Axis construction uses the mp box right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyOfBaseZero.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyOfBaseZero.lean#L41-L48

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSemilatticeSystemStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSectionsAffineFlatStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AbelianSchemeBaseChangeExistsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUniqueConstantOfCompatibleFamilyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparisonStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverCompStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatCocycleTensorRepresentationStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClassZeroCocycleTensorCoboundaryStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleOnProductFromSecondFactorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyOfBaseZero
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem GlobalTheory.CompanionTheory.Axis.mp_box_right (a : C) {T T' : C} (ψ : T ⟶ T') (u : F.obj a ⊗[R] F.obj T) :
    mp (box F) (show ((a, T) : C × C) ⟶ (a, T') from (𝟙 a, ψ)) u = (mp F ψ).toLinearMap.lTensor _ u := by sorry
