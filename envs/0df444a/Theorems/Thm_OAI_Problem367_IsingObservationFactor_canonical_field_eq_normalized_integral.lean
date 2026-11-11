-- Prove2me | Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonical_field_eq_normalized_integral
-- name    : OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:46:49.513679+00:00
-- url     : https://prove2.me/theorems/7f44ec95-44a3-4ace-8f97-23ef221dafe7
-- title:
--   OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral` of [lean/OAI/Probability/FreeIsing/Ising/CanonicalNormalizedField.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalNormalizedField.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingObservationFactor`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`, `open IsingObservationInnovation BrownianGrid`):
--
--   ```lean
--   theorem canonical_field_eq_normalized_integral
--       {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       [IsProbabilityMeasure μ]
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       {J : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Z : ℝ≥0 → Paths d → ℝ}
--       (hJM : ∀ a, Martingale (J a) (filtration d) (observationLaw μ))
--       (hZM : Martingale Z (filtration d) (observationLaw μ))
--       (hJ2 : ∀ a t, MemLp (J a t) 2 (observationLaw μ))
--       (hZ2 : ∀ t, MemLp (Z t) 2 (observationLaw μ))
--       (hcJ : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J a t x))
--       (hcZ : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => Z t x))
--       (hsumJ : ∀ t, HasSum (fun a => (hJ2 a t).toLp (J a t)) ((hZ2 t).toLp (Z t)))
--       (hJlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
--         Tendsto (fun k => ∫ x,
--           (BrownianIntegralProcess.stoppedUniformSum
--             (fun s x => innovationMap beta x a s) (continuousRootResponse hb a)
--             N k t x - J a t x) ^ 2 ∂observationLaw μ) atTop (𝓝 0)) :
--       ∀ᵐ x ∂observationLaw μ, ∀ t,
--         continuousField beta (ConnectedHull.root d) t x = Z t x +
--           nnrealTimePrimitive (canonicalResponseDrift beta (ConnectedHull.root d)) t x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.nnrealTimePrimitive`, `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.IsingObservationInnovation.filtration`, `OAI.Problem367.IsingObservationInnovation.innovationMap`, `OAI.Problem367.IsingObservationInnovation.observationLaw`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.BrownianIntegralProcess.stoppedUniformSum` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.IsingObservationFactor.canonicalResponseDrift`, `OAI.Problem367.IsingObservationFactor.continuousField` and `OAI.Problem367.IsingObservationFactor.continuousRootResponse` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.actual_variance_analysis` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalNormalizedField.lean (declaration OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation BrownianGrid

theorem canonical_field_eq_normalized_integral
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {J : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Z : ℝ≥0 → Paths d → ℝ}
    (hJM : ∀ a, Martingale (J a) (filtration d) (observationLaw μ))
    (hZM : Martingale Z (filtration d) (observationLaw μ))
    (hJ2 : ∀ a t, MemLp (J a t) 2 (observationLaw μ))
    (hZ2 : ∀ t, MemLp (Z t) 2 (observationLaw μ))
    (hcJ : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J a t x))
    (hcZ : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => Z t x))
    (hsumJ : ∀ t, HasSum (fun a => (hJ2 a t).toLp (J a t)) ((hZ2 t).toLp (Z t)))
    (hJlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun k => ∫ x,
        (BrownianIntegralProcess.stoppedUniformSum
          (fun s x => innovationMap beta x a s) (continuousRootResponse hb a)
          N k t x - J a t x) ^ 2 ∂observationLaw μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂observationLaw μ, ∀ t,
      continuousField beta (ConnectedHull.root d) t x = Z t x +
        nnrealTimePrimitive (canonicalResponseDrift beta (ConnectedHull.root d)) t x := by
  sorry

end Problem367.IsingObservationFactor

end

end OAI
end
