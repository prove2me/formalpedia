-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_eventually_small_endpoints_slice_q44
-- name    : OAI.StandardMapEntropy.eventually_small_endpoints_slice_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:07:05.263616+00:00
-- url     : https://prove2.me/theorems/627377e6-42f7-4321-b1a3-49508bcebbaf
-- title:
--   OAI.StandardMapEntropy.eventually_small_endpoints_slice_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.eventually_small_endpoints_slice` of [lean/OAI/Dynamics/StandardMap/StandardMap/CancellationScalar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/CancellationScalar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped Topology ENNReal`):
--
--   ```lean
--   theorem eventually_small_endpoints_slice_q44 :
--       ∃ M₀ : ℝ, ∀ k : ℝ, 0 < k → M₀ ≤ growthBase k →
--         ∀ q : ℝ, ∀ n Np Nm : ℕ, 10000000 ≤ n → n ≤ Np ∧ Np ≤ n+1 → n ≤ Nm ∧ Nm ≤ n+1 →
--         volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
--           pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤
--             3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) ∧
--           pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤
--             3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))} ≤ ENNReal.ofReal ((1/4:ℝ)^n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.growthBase`, `OAI.StandardMapEntropy.linearSolution`, `OAI.StandardMapEntropy.orbitCoefficient`, `OAI.StandardMapEntropy.pairMagnitude`, `OAI.StandardMapEntropy.phi` and `OAI.StandardMapEntropy.potential` (definitions bundle `OAIQ44C000` of this split).
--
--   **Used by.** The proofs of `OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aemulti_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aeterminal_q44` and `OAI.StandardMapEntropy.eventually_meanDeficit_doubling_q44` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/CancellationScalar.lean (declaration OAI.StandardMapEntropy.eventually_small_endpoints_slice)

import Mathlib
import Definitions.Def_OAIQ44C000

section

attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

theorem eventually_small_endpoints_slice_q44 :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0 < k → M₀ ≤ growthBase k →
      ∀ q : ℝ, ∀ n Np Nm : ℕ, 10000000 ≤ n → n ≤ Np ∧ Np ≤ n+1 → n ≤ Nm ∧ Nm ≤ n+1 →
      volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
        pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤
          3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) ∧
        pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤
          3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))} ≤ ENNReal.ofReal ((1/4:ℝ)^n) := by
  sorry
end StandardMapEntropy

end OAI
end
