-- Prove2me | Theorems.Thm_GlobalTheory_exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial
-- name    : GlobalTheory.exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:17.778528+00:00
-- url     : https://prove2.me/theorems/f7d57053-4308-468e-842e-0cada80d7607
-- title:
--   Global Theory: exists sec nonzero Locus eq of is Affine Open of factorial
-- statement:
--   The Global Theory construction uses the exists sec nonzero Locus eq of is Affine Open of factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecNonzeroLocusEqOfIsAffineOpenOfFactorial.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecNonzeroLocusEqOfIsAffineOpenOfFactorial.lean#L18-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNonzeroLocusEqAffineOpenLocallyFactorialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecNonzeroLocusEqOfIsAffineOpenOfFactorial
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
open GlobalTheory

theorem GlobalTheory.exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated], (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty → ∃ (L : LB X) (s : LB.Sec L), L.IsLB ∧ nonzeroLocus s = U := by sorry
