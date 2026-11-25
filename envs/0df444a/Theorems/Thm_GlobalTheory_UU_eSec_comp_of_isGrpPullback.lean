-- Prove2me | Theorems.Thm_GlobalTheory_UU_eSec_comp_of_isGrpPullback
-- name    : GlobalTheory.UU.eSec_comp_of_isGrpPullback
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:29.098886+00:00
-- url     : https://prove2.me/theorems/dc47d182-4dac-446a-ba64-eb5aa689f1ab
-- title:
--   UU: e Sec comp of is Grp Pullback
-- statement:
--   The UU construction uses the e Sec comp of is Grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ESecCompOfIsGrpPullback.lean#L74-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ESecCompOfIsGrpPullback.lean#L74-L91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ESecCompOfIsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem GlobalTheory.UU.eSec_comp_of_isGrpPullback {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by sorry
