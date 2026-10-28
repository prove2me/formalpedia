-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_BridgeScalarControl_prefix_dirichlet_q44
-- name    : OAI.StandardMapEntropy.BridgeScalarControl.prefix_dirichlet_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:07:52.250355+00:00
-- url     : https://prove2.me/theorems/ed5acd45-3dc4-4be3-8e8c-171fe09f22b5
-- title:
--   OAI.StandardMapEntropy.BridgeScalarControl.prefix_dirichlet_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.BridgeScalarControl.prefix_dirichlet` of [lean/OAI/Dynamics/StandardMap/StandardMap/BridgeScalars.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BridgeScalars.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open Set Filter Metric`, `open scoped Topology`):
--
--   ```lean
--   lemma BridgeScalarControl.prefix_dirichlet_q44 {k : ℝ} (h : BridgeScalarControl k)
--       (B n : ℕ) (hn : 1 ≤ n) (hB : B=n ∨ B=n+1) (hBn : 2 ≤ B)
--       (z : ℝ × ℝ) (hz : prefixEligible k B (n+1) z) :
--       tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0 ∧ ∀ p, 1 ≤ p → p ≤ n →
--         |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
--           12*growthBase k^(-(9/10:ℝ)*(p:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.BridgeScalarControl`, `OAI.StandardMapEntropy.growthBase`, `OAI.StandardMapEntropy.orbitCoefficient` and `OAI.StandardMapEntropy.tSolution` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.dirichletSolution` and `OAI.StandardMapEntropy.prefixEligible` (definitions bundle `OAIQ44C002` of this split).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.actual_grid_square_product_q44` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BridgeScalars.lean (declaration OAI.StandardMapEntropy.BridgeScalarControl.prefix_dirichlet)

import Mathlib
import Definitions.Def_OAIQ44C002

section

attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma BridgeScalarControl.prefix_dirichlet_q44 {k : ℝ} (h : BridgeScalarControl k)
    (B n : ℕ) (hn : 1 ≤ n) (hB : B=n ∨ B=n+1) (hBn : 2 ≤ B)
    (z : ℝ × ℝ) (hz : prefixEligible k B (n+1) z) :
    tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0 ∧ ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)) := by
  sorry
end StandardMapEntropy

end OAI
end
