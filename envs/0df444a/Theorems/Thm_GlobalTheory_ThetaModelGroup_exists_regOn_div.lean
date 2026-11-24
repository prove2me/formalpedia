-- Prove2me | Theorems.Thm_GlobalTheory_ThetaModelGroup_exists_regOn_div
-- name    : GlobalTheory.ThetaModelGroup.exists_regOn_div
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:15.77385+00:00
-- url     : https://prove2.me/theorems/f2c2ddfb-4eed-4aa6-93da-f6f1fd8c1644
-- title:
--   Theta Model Group: exists reg On div
-- statement:
--   The Theta Model Group construction uses the exists reg On div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean#L123-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean#L123-L138

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

theorem GlobalTheory.ThetaModelGroup.exists_regOn_div {κ : Type} [Finite κ] {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y}
    {s : κ → (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (h : ∀ c, RegAt y (s c)) (c : κ) (hc : s c y ≠ 0) :
    ∃ U : Y.left.Opens, ⊤ ≤ y.left ⁻¹ᵁ U ∧ (∀ y' : 𝟙_ (Over (Sp ℂ)) ⟶ Y, ⊤ ≤ y'.left ⁻¹ᵁ U → s c y' ≠ 0) ∧
      ∀ c', RegOn U (fun y' => s c' y' / s c y') := by sorry
