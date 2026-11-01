-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_MildCollisionSolution_localAdmissible_q80
-- name    : OAI.BoltzmannNonuniqueness.MildCollisionSolution.localAdmissible_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:15:35.785526+00:00
-- url     : https://prove2.me/theorems/5f992a35-6317-4608-98b5-d286048a1751
-- title:
--   OAI.BoltzmannNonuniqueness.MildCollisionSolution.localAdmissible_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.MildCollisionSolution.localAdmissible` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/MildLocalAdmissibility.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/MildLocalAdmissibility.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.MildCollisionSolution`, with `open MeasureTheory Set`, `open scoped ENNReal`):
--
--   ```lean
--   theorem localAdmissible_q80 {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}
--       (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
--       (hf₀m : Measurable f₀) (hf₀n : ∀ p, 0 ≤ f₀ p) (hf₀ : FiniteEntropyDatum f₀)
--       (hfinite : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (positiveEvolution T f₀ g t))
--       (hH : ∀ t ∈ Icc 0 T,
--         ENNReal.ofReal (relativeEntropy (positiveEvolution T f₀ g t))+
--         (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (positiveEvolution T f₀ g s)) ≤
--           ENNReal.ofReal (relativeEntropy f₀))
--       (hE : Integrable (CollisionCompactness.exponentialPair g)
--         ((AnnularEnvelope.timePositionVolume T).prod volume)) :
--       AdmissibleLocal T f₀ (positiveEvolution T f₀ g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.AdmissibleLocal`, `OAI.BoltzmannNonuniqueness.MildCollisionSolution`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.timePositionVolume`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.exponentialPair` and `OAI.BoltzmannNonuniqueness.MildCollisionSolution.positiveEvolution` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Density`, `OAI.BoltzmannNonuniqueness.FiniteEntropyDatum`, `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position`, `OAI.BoltzmannNonuniqueness.Velocity`, `OAI.BoltzmannNonuniqueness.entropyDissipation` and `OAI.BoltzmannNonuniqueness.relativeEntropy` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_limit_q80` and `OAI.BoltzmannNonuniqueness.nonuniqueness_without_compactness_inputs_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/MildLocalAdmissibility.lean (declaration OAI.BoltzmannNonuniqueness.MildCollisionSolution.localAdmissible)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A000

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.MildCollisionSolution

theorem localAdmissible_q80 {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀n : ∀ p, 0 ≤ f₀ p) (hf₀ : FiniteEntropyDatum f₀)
    (hfinite : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (positiveEvolution T f₀ g t))
    (hH : ∀ t ∈ Icc 0 T,
      ENNReal.ofReal (relativeEntropy (positiveEvolution T f₀ g t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (positiveEvolution T f₀ g s)) ≤
        ENNReal.ofReal (relativeEntropy f₀))
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) :
    AdmissibleLocal T f₀ (positiveEvolution T f₀ g) := by
  sorry

end BoltzmannNonuniqueness.MildCollisionSolution

end

end OAI
end
