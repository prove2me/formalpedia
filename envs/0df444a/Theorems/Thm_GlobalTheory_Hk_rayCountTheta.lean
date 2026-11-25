-- Prove2me | Theorems.Thm_GlobalTheory_Hk_rayCountTheta
-- name    : GlobalTheory.Hk.rayCountTheta
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:36:23.927381+00:00
-- url     : https://prove2.me/theorems/30ccc7e2-c75c-4342-bac1-6bc68c8e3960
-- title:
--   Hk: ray Count Theta
-- statement:
--   The Hk construction uses the ray Count Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayCountThetaFibreCount.lean#L53-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayCountThetaFibreCount.lean#L53-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayCountThetaFibreCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk

theorem GlobalTheory.Hk.rayCountTheta : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, ∀ g : D.G, (∀ y : ℝ, 1 ≤ y → |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, aRay D g n - 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) * y| ≤ 10 * Real.sqrt y) ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |∑' n : ℕ, aRay D g n * Real.exp (-(t * n)) - 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) / t| ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 * t := by sorry
