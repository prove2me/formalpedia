-- Prove2me | Theorems.Thm_GlobalTheory_ZetaWide_scaled
-- name    : GlobalTheory.ZetaWide.scaled
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:04.846004+00:00
-- url     : https://prove2.me/theorems/3c07d86b-1900-419d-a3cc-14a3ef662afa
-- title:
--   Zeta Wide: scaled
-- statement:
--   The Zeta Wide construction uses the scaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsMore.lean#L9-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsMore.lean#L9-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ZetaWide

theorem GlobalTheory.ZetaWide.scaled : ∃ C : ℝ, 0 < C ∧ ∀ (F : ℂ → ℂ) (c : ℂ) (M : ℝ), Differentiable ℂ F → F c ≠ 0 →
    (∀ w, ‖w - c‖ ≤ 15/4 → ‖F w‖ ≤ M) →
    ({w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0}.Finite ∧
      (∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0}, (analyticOrderNatAt F w : ℝ))
        ≤ C * (1 + Real.log (M / ‖F c‖))) ∧
    ∀ s : ℂ, ‖s - c‖ ≤ 3 → F s ≠ 0 →
      ‖deriv F s / F s - ∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0},
        (analyticOrderNatAt F w : ℂ) / (s - w)‖ ≤ C * (1 + Real.log (M / ‖F c‖)) := by sorry
