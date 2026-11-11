-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_heavyRestrictedPeakTransport_incoming_ae
-- name    : OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:19:48.172971+00:00
-- url     : https://prove2.me/theorems/83dff99a-0484-4b53-a2ee-83078449a4dc
-- title:
--   OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae` of [lean/OAI/Probability/CriticalPercolation/Modular/HeavyThinning.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/HeavyThinning.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory Filter`, `open scoped Classical ENNReal Topology BigOperators`, `open BernoulliProduct`):
--
--   ```lean
--   lemma heavyRestrictedPeakTransport_incoming_ae
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       {p q : unitInterval} (hqp : q≤p) (y : V) :
--       ∀ᵐ u ∂markLaw, (∑' x, G.heavyRestrictedPeakTransport p q u x y * G.stabilizerWeight y x) =
--         if G.heavyFlag p u y then G.peakReturn (atParameter q u) y else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BernoulliProduct.atParameter`, `OAI.CriticalPercolation.BernoulliProduct.markLaw`, `OAI.CriticalPercolation.BondGraph.heavyFlag`, `OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport`, `OAI.CriticalPercolation.BondGraph.peakReturn` and `OAI.CriticalPercolation.BondGraph.stabilizerWeight` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/HeavyThinning.lean (declaration OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae)

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

lemma heavyRestrictedPeakTransport_incoming_ae
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    {p q : unitInterval} (hqp : q≤p) (y : V) :
    ∀ᵐ u ∂markLaw, (∑' x, G.heavyRestrictedPeakTransport p q u x y * G.stabilizerWeight y x) =
      if G.heavyFlag p u y then G.peakReturn (atParameter q u) y else 0 := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
