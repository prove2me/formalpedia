-- Prove2me | Theorems.Thm_GlobalTheory_ZM_RepBC_secCoord_pull
-- name    : GlobalTheory.ZM.RepBC.secCoord_pull
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:16:13.864922+00:00
-- url     : https://prove2.me/theorems/18b2834d-0ba9-4556-83c8-45838efe1796
-- title:
--   Rep BC: sec Coord pull
-- statement:
--   The Rep BC construction uses the sec Coord pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ProjectiveRepresentationPullbackCoordinates.lean#L87-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ProjectiveRepresentationPullbackCoordinates.lean#L87-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.ZM.RepBC.secCoord_pull {σ : Type} (M : LB X) (th : σ → M.Sec) (π : Y ⟶ X) {T : Type} [CommRing T] (x : Sp T ⟶ Y)
    (v : σ → T) : SecCoord (M.pull π) (fun i => secPull M π (th i)) x v ↔ SecCoord M th (x ≫ π) v := by sorry
