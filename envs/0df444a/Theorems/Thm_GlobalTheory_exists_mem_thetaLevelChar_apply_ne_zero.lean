-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_thetaLevelChar_apply_ne_zero
-- name    : GlobalTheory.exists_mem_thetaLevelChar_apply_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:57:36.766349+00:00
-- url     : https://prove2.me/theorems/8986e128-5c26-566d-aefc-78e09478db11
-- title:
--   Global Theory: exists mem theta Level Char apply ne zero
-- statement:
--   The Global Theory construction uses the exists mem theta Level Char apply ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsMemThetaLevelCharApplyNeZero.lean#L157-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsMemThetaLevelCharApplyNeZero.lean#L157-L194

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMemThetaLevelCharApplyNeZero
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
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℝ}

theorem GlobalTheory.exists_mem_thetaLevelChar_apply_ne_zero (hτ : τ ∈ SiegelH (Fin g)) (a b : Fin g → ℝ)
    {k : ℕ} (hk : k ≠ 0) (z₀ : Fin g → ℂ) : ∃ F ∈ thetaLevelChar a b (k + 1) τ, F z₀ ≠ 0 := by sorry
