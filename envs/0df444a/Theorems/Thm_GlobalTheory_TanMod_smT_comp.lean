-- Prove2me | Theorems.Thm_GlobalTheory_TanMod_smT_comp
-- name    : GlobalTheory.TanMod.smT_comp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:16.917059+00:00
-- url     : https://prove2.me/theorems/f7bf779f-d466-58da-b5d4-25034d89022a
-- title:
--   Tan Mod: sm T comp
-- statement:
--   The Tan Mod construction uses the sm T comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsTangentModuleUniversalGroup.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsTangentModuleUniversalGroup.lean#L110-L112

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

theorem GlobalTheory.TanMod.smT_comp {G' : Over X0} (a : S) (v : overAt x0 (DualNumber S) ⟶ G) (φ : G ⟶ G') :
    homAt x0 (tm (a • (LinearMap.id : S →ₗ[S] S))) ≫ (v ≫ φ) = smT x0 a v ≫ φ := by sorry
