-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_tendsto_expected_heavy_peakReturn
-- name    : OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:26.888001+00:00
-- url     : https://prove2.me/theorems/ed6ef9d8-b228-4f0e-b54e-c55fb6920357
-- title:
--   OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn` of [lean/OAI/Probability/CriticalPercolation/Modular/HeavyThinning.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/HeavyThinning.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory Filter`, `open scoped Classical ENNReal Topology BigOperators`, `open BernoulliProduct`):
--
--   ```lean
--   lemma tendsto_expected_heavy_peakReturn
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
--       (hqp : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) (x : V) :
--       Tendsto (fun n => ∫⁻ u, if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0 ∂markLaw)
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BernoulliProduct.atParameter`, `OAI.CriticalPercolation.BernoulliProduct.markLaw`, `OAI.CriticalPercolation.BondGraph.heavyFlag` and `OAI.CriticalPercolation.BondGraph.peakReturn` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/HeavyThinning.lean (declaration OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn)

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma tendsto_expected_heavy_peakReturn
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) (x : V) :
    Tendsto (fun n => ∫⁻ u, if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0 ∂markLaw)
      atTop (𝓝 0) := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
