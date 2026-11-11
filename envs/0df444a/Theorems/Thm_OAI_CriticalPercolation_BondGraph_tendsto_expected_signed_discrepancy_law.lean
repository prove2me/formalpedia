-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_tendsto_expected_signed_discrepancy_law
-- name    : OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:22:25.638632+00:00
-- url     : https://prove2.me/theorems/50593be2-e848-4f0b-a58f-7223011b6c0b
-- title:
--   OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law` of [lean/OAI/Probability/CriticalPercolation/Modular/CriticalHeavyDrop.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/CriticalHeavyDrop.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory Filter`, `open scoped Classical ENNReal Topology BigOperators`, `open BernoulliProduct`):
--
--   ```lean
--   lemma tendsto_expected_signed_discrepancy_law (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
--       (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
--       (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
--       (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p)) :
--       Tendsto (fun n => ∑ x∈(G.orbitRepresentatives hq).roots,
--         ∫ ω, G.normalizedSignedDiscrepancy (q n) ω x ∂G.law (q n)) atTop
--         (𝓝 (∑ x∈(G.orbitRepresentatives hq).roots,
--           ∫ ω, G.normalizedSignedDiscrepancy p ω x ∂G.law p))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.incidentEdges`, `OAI.CriticalPercolation.BondGraph.normalizedSignedDiscrepancy`, `OAI.CriticalPercolation.BondGraph.orbitRepresentatives`, `OAI.CriticalPercolation.BondGraph.vertexBall` and `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.fullGraph` and `OAI.CriticalPercolation.BondGraph.law` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/CriticalHeavyDrop.lean (declaration OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law)

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

variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma tendsto_expected_signed_discrepancy_law (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => ∑ x∈(G.orbitRepresentatives hq).roots,
      ∫ ω, G.normalizedSignedDiscrepancy (q n) ω x ∂G.law (q n)) atTop
      (𝓝 (∑ x∈(G.orbitRepresentatives hq).roots,
        ∫ ω, G.normalizedSignedDiscrepancy p ω x ∂G.law p)) := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
