-- Prove2me | Theorems.Thm_GlobalTheory_Hk_tsum_exp_eq_integral
-- name    : GlobalTheory.Hk.tsum_exp_eq_integral
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:37:01.678955+00:00
-- url     : https://prove2.me/theorems/57288c1e-ed29-4110-ad6e-22c371ed4bd8
-- title:
--   Hk: tsum exp eq integral
-- statement:
--   The Hk construction uses the tsum exp eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L18-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L18-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
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

theorem GlobalTheory.Hk.tsum_exp_eq_integral (c : ℕ → ℂ) (h0 : c 0 = 0) {t : ℝ} (ht : 0 < t)
    (hs : Summable (fun n : ℕ => ‖c n‖ * Real.exp (-(t * n)))) :
    ∑' n : ℕ, c n * (Real.exp (-(t * n)) : ℂ) =
      ∫ x in Set.Ioi (1 : ℝ), (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n) * ((t * Real.exp (-(t * x)) : ℝ) : ℂ) := by sorry
