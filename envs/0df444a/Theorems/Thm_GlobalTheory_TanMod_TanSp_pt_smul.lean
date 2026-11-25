-- Prove2me | Theorems.Thm_GlobalTheory_TanMod_TanSp_pt_smul
-- name    : GlobalTheory.TanMod.TanSp.pt_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:12.17875+00:00
-- url     : https://prove2.me/theorems/2daefb3f-a457-44bb-b87d-02d77f3d16d9
-- title:
--   Tan Sp: pt smul
-- statement:
--   The Tan Sp construction uses the pt smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsTangentModuleUniversalGroup.lean#L247-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsTangentModuleUniversalGroup.lean#L247-L247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TanMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)
variable {G : Over X0} [GrpObj G]
variable [IsCommMonObj G]
variable {x0}

theorem GlobalTheory.TanMod.TanSp.pt_smul (a : S) (m : TanSp x0 G) : (a • m).pt = smT x0 a m.pt := by sorry
