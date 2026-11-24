-- Prove2me | Theorems.Thm_GlobalTheory_LAtZero_exists_regular_part
-- name    : GlobalTheory.LAtZero.exists_regular_part
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:56:16.232103+00:00
-- url     : https://prove2.me/theorems/e2107014-7d46-48d7-a225-fa485225d768
-- title:
--   LAt Zero: exists regular part
-- statement:
--   The LAt Zero construction uses the exists regular part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivLFunctionNearZero.lean#L40-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivLFunctionNearZero.lean#L40-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivEqOrderDivAddAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionNearZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.LAtZero

theorem GlobalTheory.LAtZero.exists_regular_part (f e : ℂ → ℂ) (S : Set ℂ) (B : ℝ) (hS : S.Finite)
    (he : ContinuousAt e 0) (han : AnalyticAt ℂ f 0) (hne : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), f s = 0)
    (hS0 : f 0 = 0 → 0 ∈ S) (hSz : ∀ w ∈ S, f w = 0)
    (hT : ∀ w : ℂ, 0 < w.re → w.re < 1 → |w.im| < 1 → f w = 0 → w ∈ S)
    (hbig : ∀ w ∈ S, w.re ≤ 0 → w ≠ 0 → 1 ≤ ‖w‖)
    (hcount : ∑ᶠ w ∈ S, (analyticOrderNatAt f w : ℝ) ≤ B)
    (hloc : ∀ s : ℝ, 0 < s → s < 1 → f s ≠ 0 →
      ‖deriv f s / f s + e s - ∑ᶠ w ∈ S, (analyticOrderNatAt f w : ℂ) / (s - w)‖ ≤ B) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
      (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv f s / f s = (analyticOrderNatAt f 0 : ℂ) / s + h s) ∧
      ‖h 0‖ ≤ 2 * B + ‖e 0‖ +
        ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ f ρ = 0},
          ((analyticOrderNatAt f ρ : ℕ) : ℝ) / ‖ρ‖ := by sorry
