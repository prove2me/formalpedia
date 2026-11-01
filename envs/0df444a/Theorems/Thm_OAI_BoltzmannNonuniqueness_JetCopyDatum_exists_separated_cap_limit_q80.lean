-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_exists_separated_cap_limit_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_separated_cap_limit_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:26:38.053972+00:00
-- url     : https://prove2.me/theorems/0b0fec91-c77c-4f2d-b11b-69ef51c52cc1
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_separated_cap_limit_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_separated_cap_limit` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapUniformFiniteHorizon.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapUniformFiniteHorizon.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set Filter`, `open scoped Topology ENNReal`):
--
--   ```lean
--   theorem exists_separated_cap_limit_q80
--       (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
--       (hDP : Published.DunfordPettis1940Theorem321) (hDPhot : Published.DunfordPettis1940HotWindows)
--       (hDPpair : Published.DunfordPettis1940HotPairWindows)
--       (hMityagin : Published.Mityagin2020FiveGainParameters)
--       {s₀ η K α γ d₀ q : ℝ} {B : DormantFamily s₀ η K α γ d₀ q} (D : DormantLimit B)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2)
--       (hfinite : ∀ (F : ShrinkingCapFamily s₀ η K α γ d₀ q) (S : AttainedCapSequence F)
--         (E : AttainedCapSequence.HotPairExtraction S), E.horizon < ⊤) :
--       ∃ (A : TightCapFamily s₀ η K α γ d₀ q) (L : CapLocalLimit A), A.time ≤ B.time ∧
--         ∃ t ∈ Icc 0 A.time,
--           ¬ (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
--               L.density t =ᵐ[volume]
--             MildCollisionSolution.positiveEvolution B.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
--               D.density t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapLocalLimit`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.DormantFamily`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.DormantLimit`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily`, `OAI.BoltzmannNonuniqueness.JetPeriodicDatum.datum`, `OAI.BoltzmannNonuniqueness.MildCollisionSolution.positiveEvolution`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.CompactFamily` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.DunfordPettis1940HotPairWindows`, `OAI.BoltzmannNonuniqueness.Published.DunfordPettis1940HotWindows`, `OAI.BoltzmannNonuniqueness.Published.DunfordPettis1940Theorem321`, `OAI.BoltzmannNonuniqueness.Published.GLPS1988Proposition3`, `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` and `OAI.BoltzmannNonuniqueness.Published.Mityagin2020FiveGainParameters` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position` and `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.nonuniqueness_without_compactness_inputs_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapUniformFiniteHorizon.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_separated_cap_limit)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_separated_cap_limit_q80
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321) (hDPhot : Published.DunfordPettis1940HotWindows)
    (hDPpair : Published.DunfordPettis1940HotPairWindows)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {s₀ η K α γ d₀ q : ℝ} {B : DormantFamily s₀ η K α γ d₀ q} (D : DormantLimit B)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (hfinite : ∀ (F : ShrinkingCapFamily s₀ η K α γ d₀ q) (S : AttainedCapSequence F)
      (E : AttainedCapSequence.HotPairExtraction S), E.horizon < ⊤) :
    ∃ (A : TightCapFamily s₀ η K α γ d₀ q) (L : CapLocalLimit A), A.time ≤ B.time ∧
      ∃ t ∈ Icc 0 A.time,
        ¬ (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
            L.density t =ᵐ[volume]
          MildCollisionSolution.positiveEvolution B.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
            D.density t) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
