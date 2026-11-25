-- Prove2me | Theorems.Thm_GlobalTheory_T_exactAt_sectionCube_of_mul_pullback
-- name    : GlobalTheory.T.exactAt_sectionCube_of_mul_pullback
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:24:14.91916+00:00
-- url     : https://prove2.me/theorems/8a55aba6-9a8b-4048-a83c-939e2e9e2ccd
-- title:
--   T: exact At section Cube of mul pullback
-- statement:
--   The T construction uses the exact At section Cube of mul pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExactAtSectionCubeOfMulPullbackStatement.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExactAtSectionCubeOfMulPullbackStatement.lean#L19-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullbackStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

theorem GlobalTheory.T.exactAt_sectionCube_of_mul_pullback : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (N : LB P.A.left) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens) (p : ℕ), (m : K) ≠ 0 → N.IsLB → (cubeComplex (secCube P.A.hom (N.pull (Out.mulA P.A m).left) (fun i => (Out.mulA P.A m).left ⁻¹ᵁ D i))).ExactAt p → (cubeComplex (secCube P.A.hom N D)).ExactAt p := by sorry
