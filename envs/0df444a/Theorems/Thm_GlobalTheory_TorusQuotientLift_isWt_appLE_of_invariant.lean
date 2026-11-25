-- Prove2me | Theorems.Thm_GlobalTheory_TorusQuotientLift_isWt_appLE_of_invariant
-- name    : GlobalTheory.TorusQuotientLift.isWt_appLE_of_invariant
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:14:15.728096+00:00
-- url     : https://prove2.me/theorems/aa78fa25-c5d1-47cf-bafa-06113f2e0394
-- title:
--   Torus Quotient Lift: is Wt app LE of invariant
-- statement:
--   The Torus Quotient Lift construction uses the is Wt app LE of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorusQuotientSchemeOverNilpotentThickening.lean#L327-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorusQuotientSchemeOverNilpotentThickening.lean#L327-L332

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening
noncomputable section
open GlobalTheory GlobalTheory.TorusQuotientLift
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
variable {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'} {V : G.left.Opens} {V' : G'.left.Opens}

theorem GlobalTheory.TorusQuotientLift.isWt_appLE_of_invariant {Y : Scheme.{0}} (r : G.left ⟶ Y)
    (hr : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ r = g.left ≫ r)
    (U : Y.Opens) (h : V ≤ r ⁻¹ᵁ U) (c : Γ(Y, U)) : IsWt i V ((r.appLE U V h).hom c) 0 := by sorry
