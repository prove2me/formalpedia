-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_OrbitRepresentatives_tilted_massTransport_ennreal
-- name    : OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.tilted_massTransport_ennreal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:17:02.679999+00:00
-- url     : https://prove2.me/theorems/a12d9d84-0b1d-47fa-8c80-600289317839
-- title:
--   OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.tilted_massTransport_ennreal: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.tilted_massTransport_ennreal` of [lean/OAI/Probability/CriticalPercolation/Modular/TiltedTransportENNReal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/TiltedTransportENNReal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives`, with `open Set MeasureTheory`, `open scoped Classical ENNReal BigOperators`):
--
--   ```lean
--   lemma tilted_massTransport_ennreal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (F : V → V → ℝ≥0∞)
--       (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) :
--       (∑ x ∈ R.roots, ∑' y, F x y) =
--         ∑ y ∈ R.roots, ∑' x, F x y * G.stabilizerWeight y x
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives` and `OAI.CriticalPercolation.BondGraph.stabilizerWeight` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.Aut`, `OAI.CriticalPercolation.BondGraph.LocallyFinite` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.incoming_finite_ae`, `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae`, `OAI.CriticalPercolation.BondGraph.expected_weighted_peakRatio` and `OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/TiltedTransportENNReal.lean (declaration OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.tilted_massTransport_ennreal)

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
namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

lemma tilted_massTransport_ennreal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) :
    (∑ x ∈ R.roots, ∑' y, F x y) =
      ∑ y ∈ R.roots, ∑' x, F x y * G.stabilizerWeight y x := by
  sorry

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end
