-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Axis_boxCoef_left
-- name    : GlobalTheory.CompanionTheory.Axis.boxCoef_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:51.551675+00:00
-- url     : https://prove2.me/theorems/7e6569bd-8cea-4822-979f-0b74fdd84398
-- title:
--   Axis: box Coef left
-- statement:
--   The Axis construction uses the box Coef left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean#L282-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean#L282-L291

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
variable {R : Type} [CommRing R] {A : Over (Sp R)} {P : Type} [SemilatticeInf P]

theorem GlobalTheory.CompanionTheory.Axis.boxCoef_left (S : Sys A.left P) (x : HO1 A.hom) (c : HO1 (A ⊗ A).hom) (h : IsPullO (wOver (fst A A)) x c) :
    (resSys _ (boxSys S)).pull1 c = (boxCoef S).pull1 ((boxL _).pull1 ((resSys _ S).pull1 x)) := by sorry
