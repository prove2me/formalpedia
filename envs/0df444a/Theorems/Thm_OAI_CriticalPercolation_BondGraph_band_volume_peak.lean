-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_band_volume_peak
-- name    : OAI.CriticalPercolation.BondGraph.band_volume_peak
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:16:55.199135+00:00
-- url     : https://prove2.me/theorems/886128b7-66bd-4e10-a375-2138f2d54d9d
-- title:
--   OAI.CriticalPercolation.BondGraph.band_volume_peak: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.band_volume_peak` of [lean/OAI/Probability/CriticalPercolation/Modular/NormalizedDiscrepancy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/NormalizedDiscrepancy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal BigOperators`):
--
--   ```lean
--   lemma band_volume_peak (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (p : ℝ) (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) :
--       (G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)*G.peakReturn ω x =
--         ENNReal.ofReal |G.weightedDiscrepancy p ω x| *G.peakVolumeBand T U ω x
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.discrepancyVolumeBand`, `OAI.CriticalPercolation.BondGraph.normalizedClusterVolume`, `OAI.CriticalPercolation.BondGraph.peakReturn`, `OAI.CriticalPercolation.BondGraph.peakVolumeBand` and `OAI.CriticalPercolation.BondGraph.weightedDiscrepancy` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.expected_discrepancyTail_bound` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/NormalizedDiscrepancy.lean (declaration OAI.CriticalPercolation.BondGraph.band_volume_peak)

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

lemma band_volume_peak (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) :
    (G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)*G.peakReturn ω x =
      ENNReal.ofReal |G.weightedDiscrepancy p ω x| *G.peakVolumeBand T U ω x := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
