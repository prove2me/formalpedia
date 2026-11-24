-- Prove2me | Theorems.Thm_GlobalTheory_ThetaAmple_two_mul_dot_int
-- name    : GlobalTheory.ThetaAmple.two_mul_dot_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:05:03.228991+00:00
-- url     : https://prove2.me/theorems/31c51c7e-1157-47e6-94eb-67e387f56431
-- title:
--   Theta Ample: two mul dot int
-- statement:
--   The Theta Ample construction uses the two mul dot int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L199-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L199-L207

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel
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
open GlobalTheory GlobalTheory.ThetaAmple

theorem GlobalTheory.ThetaAmple.two_mul_dot_int {g : ℕ} {a : Fin g → ℝ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (n : Fin g → ℤ) :
    ∃ k : ℤ, 2 * (ofRealVec a ⬝ᵥ ofIntVec n) = k := by sorry
