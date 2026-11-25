-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Axis_pull1_surjective_of_bijective
-- name    : GlobalTheory.CompanionTheory.Axis.pull1_surjective_of_bijective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:16:50.757822+00:00
-- url     : https://prove2.me/theorems/d21319de-8a9e-4032-b1c3-a131e0573133
-- title:
--   Axis: pull1 surjective of bijective
-- statement:
--   The Axis construction uses the pull1 surjective of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean#L135-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean#L135-L162

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
open CategoryTheory.Limits
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]

theorem GlobalTheory.CompanionTheory.Axis.pull1_surjective_of_bijective (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : (Bx P)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (m : CoefMap (RingHom.id R) (box F) F') (hG : m.G = boxG P) (hb : ∀ T, Function.Bijective (m.α T)) :
    Function.Surjective m.pull1 := by sorry
