-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotPairExtraction_entry_window_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.entry_window_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:22:47.800984+00:00
-- url     : https://prove2.me/theorems/1872ec50-92ec-4f85-ac9d-51a64bfefecf
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.entry_window_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.entry_window` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapAnnularMassGrowth.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapAnnularMassGrowth.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal ProbabilityTheory`, `open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry`):
--
--   ```lean
--   theorem HotPairExtraction.entry_window_q80
--       (hDP : Published.DunfordPettis1940HotPairWindows)
--       (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
--       (E : HotPairExtraction S)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2)
--       {κ ρ ε a U V : ℝ} (hκ : 0 ≤ κ) (hκmax : κ ≤ 1) (hρ : ρ ≤ 1)
--       (hε : 0 < ε) (hεmax : ε ≤ 1/12) (hαε : α ≤ ε/2) (hερ : 6*ε ≤ ρ)
--       (haccess : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
--       (ha : 0 < a) (haU : a < U) (hUV : U < V) (hV : ENNReal.ofReal V < E.horizon)
--       (n : ℕ) :
--       ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a U → t ∈ Ioo a U →
--         0 < t-s → ((n:ℝ)+6)*(t-s) ≤ 1 →
--         0 < hotPhaseSlice E.hotLimit s
--           (flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s) →
--         0 < hotPhaseSlice E.hotLimit t (flight t ⁻¹' velocityPhaseBall κ ρ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.EuclideanFlight.flight`, `OAI.BoltzmannNonuniqueness.EuclideanFlight.hotPhaseSlice`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability`, `OAI.BoltzmannNonuniqueness.WeakTime.Phase`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotLimit` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.seedEscapeRegion`, `OAI.BoltzmannNonuniqueness.Published.DunfordPettis1940HotPairWindows`, `OAI.BoltzmannNonuniqueness.Published.GLPS1988Proposition3`, `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.accessAngles` and `OAI.BoltzmannNonuniqueness.ReferenceGeometry.velocityPhaseBall` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Sphere` and `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapAnnularMassGrowth.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.entry_window)

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
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.entry_window_q80
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {κ ρ ε a U V : ℝ} (hκ : 0 ≤ κ) (hκmax : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1/12) (hαε : α ≤ ε/2) (hερ : 6*ε ≤ ρ)
    (haccess : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (ha : 0 < a) (haU : a < U) (hUV : U < V) (hV : ENNReal.ofReal V < E.horizon)
    (n : ℕ) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a U → t ∈ Ioo a U →
      0 < t-s → ((n:ℝ)+6)*(t-s) ≤ 1 →
      0 < hotPhaseSlice E.hotLimit s
        (flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s) →
      0 < hotPhaseSlice E.hotLimit t (flight t ⁻¹' velocityPhaseBall κ ρ) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end
