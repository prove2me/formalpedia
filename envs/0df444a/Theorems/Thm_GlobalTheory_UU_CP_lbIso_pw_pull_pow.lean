-- Prove2me | Theorems.Thm_GlobalTheory_UU_CP_lbIso_pw_pull_pow
-- name    : GlobalTheory.UU.CP.lbIso_pw_pull_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:15.640577+00:00
-- url     : https://prove2.me/theorems/dd72fa6f-882d-590f-8df3-fe16926789d9
-- title:
--   CP: lb Iso pw pull pow
-- statement:
--   The CP construction uses the lb Iso pw pull pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LbIsoPwPullPowLocal.lean#L43-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LbIsoPwPullPowLocal.lean#L43-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulPullOfCubeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LbIsoPwPullPowLocal
import Theorems.Thm_GlobalTheory_MulPull_HasGen_pull

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU

theorem GlobalTheory.UU.CP.lbIso_pw_pull_pow {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ) :
    LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) := by sorry
