-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_light_zero_or_infinitely_many_ae
-- name    : OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:19:45.08982+00:00
-- url     : https://prove2.me/theorems/20bd9a63-7457-4cd1-9307-0f730e8af320
-- title:
--   OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae` of [lean/OAI/Probability/CriticalPercolation/Modular/LightClusterNumber.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/LightClusterNumber.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   theorem light_zero_or_infinitely_many_ae [Infinite V]
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (p : unitInterval) :
--       ∀ᵐ ω ∂G.law p, (∃ v, ω∈G.lightInfiniteEvent v v) → G.infinitelyManyLightClusters ω
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.infinitelyManyLightClusters` and `OAI.CriticalPercolation.BondGraph.lightInfiniteEvent` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.fullGraph` and `OAI.CriticalPercolation.BondGraph.law` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.main_all_light_or_sparse_boundary` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/LightClusterNumber.lean (declaration OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae)

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

theorem light_zero_or_infinitely_many_ae [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    ∀ᵐ ω ∂G.law p, (∃ v, ω∈G.lightInfiniteEvent v v) → G.infinitelyManyLightClusters ω := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
