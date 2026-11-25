-- Prove2me | Theorems.Thm_GlobalTheory_WtBundle_prod_psum
-- name    : GlobalTheory.WtBundle.prod_psum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:15:35.704383+00:00
-- url     : https://prove2.me/theorems/d4ef039c-cb24-49e9-bed7-1084dfd74e41
-- title:
--   Wt Bundle: prod psum
-- statement:
--   The Wt Bundle construction uses the prod psum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CommGroupCommonFactorQuotientCancel.lean#L225-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CommGroupCommonFactorQuotientCancel.lean#L225-L242

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CommGroupCommonFactorQuotientCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.WtBundle
variable {S : Scheme.{0}}

theorem GlobalTheory.WtBundle.prod_psum {B T : Over S} [GrpObj B] (x : Fin 2 → (T ⟶ B)) {U : Type} [CommGroup U] (F : (T ⟶ B) → U) :
    ∏ J : ULift.{0} (Finset (Fin 2)), F (psum B x J.down) ^ ((-1 : ℤ) ^ (2 - J.down.card)) =
      F (x 0 * x 1) * (F (x 0))⁻¹ * (F (x 1))⁻¹ * F 1 := by sorry
