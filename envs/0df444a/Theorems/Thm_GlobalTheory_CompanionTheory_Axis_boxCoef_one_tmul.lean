-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Axis_boxCoef_one_tmul
-- name    : GlobalTheory.CompanionTheory.Axis.boxCoef_one_tmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:22.864829+00:00
-- url     : https://prove2.me/theorems/4a339d21-aa9e-41ae-948c-346616db3aa3
-- title:
--   Axis: box Coef one tmul
-- statement:
--   The Axis construction uses the box Coef one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean#L276-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean#L276-L280

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

theorem GlobalTheory.CompanionTheory.Axis.boxCoef_one_tmul (S : Sys A.left P) (T : (Bx P)ᵒᵖ) (b : (OSys A.hom S).obj (op T.unop.2)) :
    (Algebra.TensorProduct.productMap (algL S T) (algR S T)) ((1 : (OSys A.hom S).obj (op T.unop.1)) ⊗ₜ[R] b) =
      algR S T b := by sorry
