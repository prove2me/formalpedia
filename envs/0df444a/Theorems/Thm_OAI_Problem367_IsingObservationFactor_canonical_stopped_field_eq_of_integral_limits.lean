-- Prove2me | Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonical_stopped_field_eq_of_integral_limits
-- name    : OAI.Problem367.IsingObservationFactor.canonical_stopped_field_eq_of_integral_limits
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:46:58.180185+00:00
-- url     : https://prove2.me/theorems/8e3eadff-6537-4f87-8f47-e6e34fab02f3
-- title:
--   OAI.Problem367.IsingObservationFactor.canonical_stopped_field_eq_of_integral_limits: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingObservationFactor.canonical_stopped_field_eq_of_integral_limits` of [lean/OAI/Probability/FreeIsing/Ising/CanonicalNormalizedField.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalNormalizedField.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingObservationFactor`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`, `open IsingObservationInnovation BrownianGrid`):
--
--   ```lean
--   theorem canonical_stopped_field_eq_of_integral_limits
--       {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       [IsProbabilityMeasure μ]
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       {I J : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Z : ℝ≥0 → Paths d → ℝ}
--       (hIp : ∀ a, IsStronglyProgressive (filtration d) (I a))
--       (hIM : ∀ a, Martingale (I a) (filtration d) (observationLaw μ))
--       (hJM : ∀ a, Martingale (J a) (filtration d) (observationLaw μ))
--       (hZM : Martingale Z (filtration d) (observationLaw μ))
--       (hI2 : ∀ a t, MemLp (I a t) 2 (observationLaw μ))
--       (hJ2 : ∀ a t, MemLp (J a t) 2 (observationLaw μ))
--       (hZ2 : ∀ t, MemLp (Z t) 2 (observationLaw μ))
--       (hcI : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => I a t x))
--       (hcJ : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J a t x))
--       (hcZ : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => Z t x))
--       (n : ℕ) (T : ℝ≥0)
--       (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T))
--         ((posterior_memLp beta μ (ConnectedHull.root d) T 2).toLp
--           (posterior beta (ConnectedHull.root d) T)))
--       (hsumJ : HasSum (fun a => (hJ2 a T).toLp (J a T)) ((hZ2 T).toLp (Z T)))
--       (hIlim : ∀ a, Tendsto (fun k => ∫ x,
--         (uniformSum (fun t x => innovationMap beta x a t)
--           (continuousRootCovariance hb a) T k x - I a T x) ^ 2 ∂observationLaw μ)
--         atTop (𝓝 0))
--       (hJlim : ∀ a, Tendsto (fun k => ∫ x,
--         (uniformSum (fun t x => innovationMap beta x a t)
--           (continuousRootResponse hb a) T k x - J a T x) ^ 2 ∂observationLaw μ)
--         atTop (𝓝 0)) :
--       let τ := canonicalPosteriorExit beta (ConnectedHull.root d) n
--       stoppedProcess (continuousField beta (ConnectedHull.root d)) τ T =ᵐ[observationLaw μ]
--         (fun x => stoppedProcess Z τ T x +
--           stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta (ConnectedHull.root d))) τ T x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.nnrealTimePrimitive`, `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.IsingObservationInnovation.filtration`, `OAI.Problem367.IsingObservationInnovation.innovationMap`, `OAI.Problem367.IsingObservationInnovation.observationLaw`, `OAI.Problem367.IsingObservationInnovation.posterior`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.BrownianGrid.uniformSum` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.IsingObservationInnovation.posterior_memLp` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.IsingObservationFactor.canonicalPosteriorExit`, `OAI.Problem367.IsingObservationFactor.canonicalResponseDrift`, `OAI.Problem367.IsingObservationFactor.continuousField`, `OAI.Problem367.IsingObservationFactor.continuousRootCovariance` and `OAI.Problem367.IsingObservationFactor.continuousRootResponse` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalNormalizedField.lean (declaration OAI.Problem367.IsingObservationFactor.canonical_stopped_field_eq_of_integral_limits)

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

theorem canonical_stopped_field_eq_of_integral_limits
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {I J : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Z : ℝ≥0 → Paths d → ℝ}
    (hIp : ∀ a, IsStronglyProgressive (filtration d) (I a))
    (hIM : ∀ a, Martingale (I a) (filtration d) (observationLaw μ))
    (hJM : ∀ a, Martingale (J a) (filtration d) (observationLaw μ))
    (hZM : Martingale Z (filtration d) (observationLaw μ))
    (hI2 : ∀ a t, MemLp (I a t) 2 (observationLaw μ))
    (hJ2 : ∀ a t, MemLp (J a t) 2 (observationLaw μ))
    (hZ2 : ∀ t, MemLp (Z t) 2 (observationLaw μ))
    (hcI : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => I a t x))
    (hcJ : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J a t x))
    (hcZ : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => Z t x))
    (n : ℕ) (T : ℝ≥0)
    (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T))
      ((posterior_memLp beta μ (ConnectedHull.root d) T 2).toLp
        (posterior beta (ConnectedHull.root d) T)))
    (hsumJ : HasSum (fun a => (hJ2 a T).toLp (J a T)) ((hZ2 T).toLp (Z T)))
    (hIlim : ∀ a, Tendsto (fun k => ∫ x,
      (uniformSum (fun t x => innovationMap beta x a t)
        (continuousRootCovariance hb a) T k x - I a T x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0))
    (hJlim : ∀ a, Tendsto (fun k => ∫ x,
      (uniformSum (fun t x => innovationMap beta x a t)
        (continuousRootResponse hb a) T k x - J a T x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0)) :
    let τ := canonicalPosteriorExit beta (ConnectedHull.root d) n
    stoppedProcess (continuousField beta (ConnectedHull.root d)) τ T =ᵐ[observationLaw μ]
      (fun x => stoppedProcess Z τ T x +
        stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta (ConnectedHull.root d))) τ T x) := by
  sorry

end Problem367.IsingObservationFactor

end

end OAI
end
