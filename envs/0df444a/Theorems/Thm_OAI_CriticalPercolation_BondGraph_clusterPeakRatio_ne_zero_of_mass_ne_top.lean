-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_clusterPeakRatio_ne_zero_of_mass_ne_top
-- name    : OAI.CriticalPercolation.BondGraph.clusterPeakRatio_ne_zero_of_mass_ne_top
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:18:22.252888+00:00
-- url     : https://prove2.me/theorems/4feaef31-92a6-45fb-9779-547baf6a54ed
-- title:
--   OAI.CriticalPercolation.BondGraph.clusterPeakRatio_ne_zero_of_mass_ne_top: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.clusterPeakRatio_ne_zero_of_mass_ne_top` of [lean/OAI/Probability/CriticalPercolation/Modular/HeavyDiscrepancy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/HeavyDiscrepancy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory Filter`, `open scoped Classical ENNReal Topology BigOperators`, `open BernoulliProduct`):
--
--   ```lean
--   lemma clusterPeakRatio_ne_zero_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (ω : Set E) (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
--       G.clusterPeakRatio ω x≠0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.clusterPeakRatio` and `OAI.CriticalPercolation.BondGraph.modularMass` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.cluster` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/HeavyDiscrepancy.lean (declaration OAI.CriticalPercolation.BondGraph.clusterPeakRatio_ne_zero_of_mass_ne_top)

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

namespace CriticalPercolation

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma clusterPeakRatio_ne_zero_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    G.clusterPeakRatio ω x≠0 := by
  sorry

end BondGraph
end CriticalPercolation
end
end

end OAI
end
