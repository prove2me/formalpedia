-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base
-- name    : OAI.CriticalPercolation.BondGraph.stabilizerWeight_change_base
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:02.507998+00:00
-- url     : https://prove2.me/theorems/b9d81553-5006-4db3-a828-7bd69ffb9a16
-- title:
--   OAI.CriticalPercolation.BondGraph.stabilizerWeight_change_base: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.stabilizerWeight_change_base` of [lean/OAI/Probability/CriticalPercolation/Modular/ModularClusterMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/ModularClusterMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   lemma stabilizerWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (o a x : V) : G.stabilizerWeight o x =
--         G.stabilizerWeight o a * G.stabilizerWeight a x
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.stabilizerWeight` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae`, `OAI.CriticalPercolation.BondGraph.band_volume_peak`, `OAI.CriticalPercolation.BondGraph.bondWeight_le_at_end`, `OAI.CriticalPercolation.BondGraph.clusterPeakRatio_le_one`, `OAI.CriticalPercolation.BondGraph.clusterPeakRatio_ne_zero_of_mass_ne_top`, `OAI.CriticalPercolation.BondGraph.expected_discrepancyTail_bound`, `OAI.CriticalPercolation.BondGraph.expected_discrepancy_peakBand_fourth`, `OAI.CriticalPercolation.BondGraph.expected_weighted_peakRatio`, `OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae`, `OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae`, `OAI.CriticalPercolation.BondGraph.main_all_light_or_sparse_boundary`, `OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial`, `OAI.CriticalPercolation.BondGraph.normalizedClusterVolume_eq_at_peak`, `OAI.CriticalPercolation.BondGraph.stabilizerWeight_le_one_iff`, `OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn` and `OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/ModularClusterMass.lean (declaration OAI.CriticalPercolation.BondGraph.stabilizerWeight_change_base)

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
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stabilizerWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a x : V) : G.stabilizerWeight o x =
      G.stabilizerWeight o a * G.stabilizerWeight a x := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
