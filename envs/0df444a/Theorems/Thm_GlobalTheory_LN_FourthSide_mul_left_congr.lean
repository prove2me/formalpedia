-- Prove2me | Theorems.Thm_GlobalTheory_LN_FourthSide_mul_left_congr
-- name    : GlobalTheory.LN.FourthSide.mul_left_congr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:11:58.185824+00:00
-- url     : https://prove2.me/theorems/ab5f59b3-9b44-5f25-8bf3-648cc7b63f00
-- title:
--   Fourth Side: mul left congr
-- statement:
--   The Fourth Side construction uses the mul left congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourthSideRespectsRigSymmetryCube.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourthSideRespectsRigSymmetryCube.lean#L25-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourthSideRespectsRigSymmetryCube
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mul_left_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.LN GlobalTheory.LN.FourthSide
variable {S Z : Scheme.{0}} {G : Over S} [GrpObj G] {s s' : Z ⟶ S}

theorem GlobalTheory.LN.FourthSide.mul_left_congr {x y : Over.mk s ⟶ G} {x' y' : Over.mk s' ⟶ G} (hx : x.left = x'.left)
    (hy : y.left = y'.left) : (x * y).left = (x' * y').left := by sorry
