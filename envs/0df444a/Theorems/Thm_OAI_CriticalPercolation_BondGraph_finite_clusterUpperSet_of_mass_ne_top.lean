-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_finite_clusterUpperSet_of_mass_ne_top
-- name    : OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_of_mass_ne_top
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:18:50.204178+00:00
-- url     : https://prove2.me/theorems/18f7e944-9674-41b3-96bb-db8167d1b691
-- title:
--   OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_of_mass_ne_top: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_of_mass_ne_top` of [lean/OAI/Probability/CriticalPercolation/Modular/ModularSuperlevels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/ModularSuperlevels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   lemma finite_clusterUpperSet_of_mass_ne_top {ω : Set E} {v : V}
--       (hm : G.modularMass v (G.cluster ω v) ≠ ∞) : (G.clusterUpperSet ω v).Finite
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.clusterUpperSet` and `OAI.CriticalPercolation.BondGraph.modularMass` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph` and `OAI.CriticalPercolation.BondGraph.cluster` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.clusterPeakRatio_le_one`, `OAI.CriticalPercolation.BondGraph.clusterPeakRatio_ne_zero_of_mass_ne_top`, `OAI.CriticalPercolation.BondGraph.clusterPeaks_finite_of_mass_ne_top`, `OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae`, `OAI.CriticalPercolation.BondGraph.main_all_light_or_sparse_boundary` and `OAI.CriticalPercolation.BondGraph.normalizedClusterVolume_eq_at_peak` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/ModularSuperlevels.lean (declaration OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_of_mass_ne_top)

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
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finite_clusterUpperSet_of_mass_ne_top {ω : Set E} {v : V}
    (hm : G.modularMass v (G.cluster ω v) ≠ ∞) : (G.clusterUpperSet ω v).Finite := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
