-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_uniform_late_zero_parameters_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.uniform_late_zero_parameters_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:23:09.912713+00:00
-- url     : https://prove2.me/theorems/759c8d2c-2698-4146-9f3b-dacd3cf127ed
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.uniform_late_zero_parameters_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.uniform_late_zero_parameters` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapAnnularMassGrowth.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapAnnularMassGrowth.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry`):
--
--   ```lean
--   theorem uniform_late_zero_parameters_q80 {d κ : ℝ}
--       (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
--       (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
--       ∃ A₀ ε γ₀ : ℝ, 0 < A₀ ∧ 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
--         ∀ {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
--           {S : AttainedCapSequence F},
--         Published.DunfordPettis1940HotPairWindows → Published.GPV2009CarlemanInput →
--         Published.GLPS1988Proposition3 → ∀ E : HotPairExtraction S,
--         0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
--         0 < K → 0 < α → α ≤ 1/4 → 0 < γ → 0 < d₀ → d₀ ≤ 1 →
--         JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1 → 1 < q → q < 2 →
--         η ≤ Real.log (1+ε/20) → α ≤ ε → γ ≤ γ₀ → 480*(8*A₀) ≤ ε*K →
--         E.horizon = ⊤ → ∃ R : ℝ, 0 < R ∧
--           ∀ᵐ t ∂volume, R < t → hotLateBoxMass E.hotLimit κ d t = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.EuclideanFlight.hotLateBoxMass`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotLimit` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.ReferenceGeometry.referenceClock` and `OAI.BoltzmannNonuniqueness.ReferenceGeometry.referenceGrowth` (definitions bundle `OAIQ080A001` of this split); `OAI.BoltzmannNonuniqueness.Published.DunfordPettis1940HotPairWindows`, `OAI.BoltzmannNonuniqueness.Published.GLPS1988Proposition3` and `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapAnnularMassGrowth.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.uniform_late_zero_parameters)

import Mathlib
import Definitions.Def_OAIQ080A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

theorem uniform_late_zero_parameters_q80 {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ ε γ₀ : ℝ, 0 < A₀ ∧ 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
        {S : AttainedCapSequence F},
      Published.DunfordPettis1940HotPairWindows → Published.GPV2009CarlemanInput →
      Published.GLPS1988Proposition3 → ∀ E : HotPairExtraction S,
      0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
      0 < K → 0 < α → α ≤ 1/4 → 0 < γ → 0 < d₀ → d₀ ≤ 1 →
      JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1 → 1 < q → q < 2 →
      η ≤ Real.log (1+ε/20) → α ≤ ε → γ ≤ γ₀ → 480*(8*A₀) ≤ ε*K →
      E.horizon = ⊤ → ∃ R : ℝ, 0 < R ∧
        ∀ᵐ t ∂volume, R < t → hotLateBoxMass E.hotLimit κ d t = 0 := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end
