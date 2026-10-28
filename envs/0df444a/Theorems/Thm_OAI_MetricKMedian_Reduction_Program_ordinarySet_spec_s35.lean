-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Reduction_Program_ordinarySet_spec_s35
-- name    : OAI.MetricKMedian.Reduction.Program.ordinarySet_spec_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:49:35.25699+00:00
-- url     : https://prove2.me/theorems/b660d7bc-fa19-4ceb-9ddb-a2fb3e177764
-- title:
--   OAI.MetricKMedian.Reduction.Program.ordinarySet_spec_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Reduction.Program`, with `open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly`, `open SparseGraph.ListOperation (Row Table setView)`, `open InstanceProgram (Raw view)`):
--
--   ```lean
--    theorem ordinarySet_spec_s35 (α ξ : ℝ) (hc : 0 < c) (hδ : 0<(δ:ℝ)) (hsmall : (δ:ℝ)≤1/6) (hξ : 0<ξ)
--       (hfactor : 1+12*(δ:ℝ)≤α+ξ) (ha : (3/2:ℝ)≤a*((δ:ℝ)*ξ/(2*c))) (hb : 6*(α+ξ)*c/((δ:ℝ)*ξ)≤(b:ℝ))
--       (hpseudo : ∀ I : Instance, I.computedPseudo r hr p c⊆I.facilities ∧ (I.computedPseudo r hr p c).Nonempty ∧
--         (I.computedPseudo r hr p c).card≤I.k+c ∧ cost I (I.computedPseudo r hr p c)≤α*optimum I)
--       (I : Instance) : ordinarySet r hr p c a b δ I⊆I.facilities ∧ (ordinarySet r hr p c a b δ I).Nonempty ∧
--         (ordinarySet r hr p c a b δ I).card≤I.k ∧ cost I (ordinarySet r hr p c a b δ I)≤(α+ξ)*optimum I
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Preparation.RationalAllParameters` (definitions bundle `OAIQ035K033` of this split); `OAI.MetricKMedian.Instance.computedPseudo` (definitions bundle `OAIQ035K062` of this split); `OAI.MetricKMedian.Reduction.Program.ordinarySet` (definitions bundle `OAIQ035K074` of this split); `OAI.MetricKMedian.Instance`, `OAI.MetricKMedian.cost` and `OAI.MetricKMedian.optimum` (the published bundle `Def_MetricKMedian`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.main_finite_work` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K074

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
 theorem ordinarySet_spec_s35 (α ξ : ℝ) (hc : 0 < c) (hδ : 0<(δ:ℝ)) (hsmall : (δ:ℝ)≤1/6) (hξ : 0<ξ)
    (hfactor : 1+12*(δ:ℝ)≤α+ξ) (ha : (3/2:ℝ)≤a*((δ:ℝ)*ξ/(2*c))) (hb : 6*(α+ξ)*c/((δ:ℝ)*ξ)≤(b:ℝ))
    (hpseudo : ∀ I : Instance, I.computedPseudo r hr p c⊆I.facilities ∧ (I.computedPseudo r hr p c).Nonempty ∧
      (I.computedPseudo r hr p c).card≤I.k+c ∧ cost I (I.computedPseudo r hr p c)≤α*optimum I)
    (I : Instance) : ordinarySet r hr p c a b δ I⊆I.facilities ∧ (ordinarySet r hr p c a b δ I).Nonempty ∧
      (ordinarySet r hr p c a b δ I).card≤I.k ∧ cost I (ordinarySet r hr p c a b δ I)≤(α+ξ)*optimum I := by
  sorry
end MetricKMedian.Reduction.Program
end

end OAI
end
