-- Prove2me | Theorems.Thm_GlobalTheory_LAtZero_norm_limit_le
-- name    : GlobalTheory.LAtZero.norm_limit_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:56:09.940122+00:00
-- url     : https://prove2.me/theorems/993d9ddc-058e-4bf1-9312-af78584b1c4c
-- title:
--   LAt Zero: norm limit le
-- statement:
--   The LAt Zero construction uses the norm limit le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivLFunctionNearZero.lean#L10-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivLFunctionNearZero.lean#L10-L38

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

theorem GlobalTheory.LAtZero.norm_limit_le (F h e : ℂ → ℂ) (P : ℂ → Prop) (Z : Finset ℂ) (m : ℂ → ℕ) (B : ℝ)
    (hh : ContinuousAt h 0) (he : ContinuousAt e 0) (h0 : 0 ∉ Z → m 0 = 0)
    (hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), P s ∧ F s = (m 0 : ℂ) / s + h s)
    (hloc : ∀ s : ℝ, 0 < s → s < 1 → P s → ‖F s + e s - ∑ w ∈ Z, (m w : ℂ) / (s - w)‖ ≤ B) :
    ‖h 0 + e 0 - ∑ w ∈ Z.erase 0, (m w : ℂ) / (0 - w)‖ ≤ B := by sorry
