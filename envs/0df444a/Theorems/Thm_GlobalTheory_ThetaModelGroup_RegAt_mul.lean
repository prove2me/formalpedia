-- Prove2me | Theorems.Thm_GlobalTheory_ThetaModelGroup_RegAt_mul
-- name    : GlobalTheory.ThetaModelGroup.RegAt.mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:46.446688+00:00
-- url     : https://prove2.me/theorems/e69d7154-00da-46a4-a60d-c009e1ad036b
-- title:
--   Reg At: mul
-- statement:
--   The Reg At construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean#L101-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean#L101-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaModelGroup
variable {X Y : Over (Sp ℂ)}

theorem GlobalTheory.ThetaModelGroup.RegAt.mul {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y} {s t : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (hs : RegAt y s) (ht : RegAt y t) :
    RegAt y (fun y' => s y' * t y') := by sorry
