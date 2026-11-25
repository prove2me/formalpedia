-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Axis_boxCoef_bijective
-- name    : GlobalTheory.CompanionTheory.Axis.boxCoef_bijective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:16.218801+00:00
-- url     : https://prove2.me/theorems/a13013ac-be15-4c39-8143-168dd4f2d542
-- title:
--   Axis: box Coef bijective
-- statement:
--   The Axis construction uses the box Coef bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean#L263-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean#L263-L265

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

theorem GlobalTheory.CompanionTheory.Axis.boxCoef_bijective (S : Sys A.left P) (T : (Bx P)ᵒᵖ) : Function.Bijective ((boxCoef S).α T) := by sorry
