-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_expected_weighted_peakRatio
-- name    : OAI.CriticalPercolation.BondGraph.expected_weighted_peakRatio
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:19:23.945101+00:00
-- url     : https://prove2.me/theorems/b7925812-0b5c-4859-b080-2005fc8d2a74
-- title:
--   OAI.CriticalPercolation.BondGraph.expected_weighted_peakRatio: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.expected_weighted_peakRatio` of [lean/OAI/Probability/CriticalPercolation/Modular/WeightedPeakTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/WeightedPeakTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal BigOperators`):
--
--   ```lean
--   theorem expected_weighted_peakRatio [Countable V] [Countable E]
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (p : unitInterval) (F : (Set E) → V → ℝ≥0∞)
--       (hm : ∀ x, Measurable (fun ω => F ω x))
--       (ha : ∀ (φ : G.Aut) ω x, F (φ.edge '' ω) (φ.vertex x)=F ω x)
--       (hr : ∀ ω x y, (G.openGraph ω).Reachable x y → F ω x=F ω y) :
--       (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, F ω x*G.clusterPeakRatio ω x ∂G.law p) =
--       ∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, F ω x*G.peakReturn ω x ∂G.law p
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.clusterPeakRatio`, `OAI.CriticalPercolation.BondGraph.orbitRepresentatives`, `OAI.CriticalPercolation.BondGraph.peakReturn` and `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.Aut`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law` and `OAI.CriticalPercolation.BondGraph.openGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.expected_discrepancyTail_bound` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/WeightedPeakTransport.lean (declaration OAI.CriticalPercolation.BondGraph.expected_weighted_peakRatio)

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
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem expected_weighted_peakRatio [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (F : (Set E) → V → ℝ≥0∞)
    (hm : ∀ x, Measurable (fun ω => F ω x))
    (ha : ∀ (φ : G.Aut) ω x, F (φ.edge '' ω) (φ.vertex x)=F ω x)
    (hr : ∀ ω x y, (G.openGraph ω).Reachable x y → F ω x=F ω y) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, F ω x*G.clusterPeakRatio ω x ∂G.law p) =
    ∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, F ω x*G.peakReturn ω x ∂G.law p := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
