-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_expected_heavy_normalizedDiscrepancy_bound_bs
-- name    : OAI.CriticalPercolation.BondGraph.expected_heavy_normalizedDiscrepancy_bound_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:25:30.85353+00:00
-- url     : https://prove2.me/theorems/92e41c00-b705-4fb0-98f8-33d286a85e7a
-- title:
--   OAI.CriticalPercolation.BondGraph.expected_heavy_normalizedDiscrepancy_bound_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.expected_heavy_normalizedDiscrepancy_bound` of [lean/OAI/Probability/CriticalPercolation/Modular/HeavyDiscrepancy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/HeavyDiscrepancy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory Filter`, `open scoped Classical ENNReal Topology BigOperators`, `open BernoulliProduct`):
--
--   ```lean
--   lemma expected_heavy_normalizedDiscrepancy_bound_bs
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
--       (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p q : unitInterval) (N : ℕ)
--       (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
--       (∫⁻ u, if G.heavyFlag p u x then G.normalizedAbsoluteDiscrepancy q (atParameter q u) x else 0 ∂markLaw) ≤
--         ((D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N)) *
--           (∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 ∂markLaw) +
--         (G.orbitRepresentatives hq).roots.card *
--           ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
--             (ENNReal.ofReal (1/2:ℝ))^N*2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BernoulliProduct.atParameter`, `OAI.CriticalPercolation.BernoulliProduct.markLaw`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.clusterPeakRatio`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.heavyFlag`, `OAI.CriticalPercolation.BondGraph.incidentEdges`, `OAI.CriticalPercolation.BondGraph.normalizedAbsoluteDiscrepancy`, `OAI.CriticalPercolation.BondGraph.orbitRepresentatives`, `OAI.CriticalPercolation.BondGraph.vertexBall` and `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/HeavyDiscrepancy.lean (declaration OAI.CriticalPercolation.BondGraph.expected_heavy_normalizedDiscrepancy_bound)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma expected_heavy_normalizedDiscrepancy_bound_bs
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p q : unitInterval) (N : ℕ)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ u, if G.heavyFlag p u x then G.normalizedAbsoluteDiscrepancy q (atParameter q u) x else 0 ∂markLaw) ≤
      ((D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N)) *
        (∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 ∂markLaw) +
      (G.orbitRepresentatives hq).roots.card *
        ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
          (ENNReal.ofReal (1/2:ℝ))^N*2 := by
  sorry

end BondGraph
end CriticalPercolation
end
end

end OAI
end
