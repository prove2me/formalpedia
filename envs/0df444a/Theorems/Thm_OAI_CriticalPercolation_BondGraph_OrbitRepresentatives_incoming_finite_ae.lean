-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_OrbitRepresentatives_incoming_finite_ae
-- name    : OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.incoming_finite_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:16:38.893482+00:00
-- url     : https://prove2.me/theorems/d78c7979-3130-445b-983e-4d2e0ee640ac
-- title:
--   OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.incoming_finite_ae: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.incoming_finite_ae` of [lean/OAI/Probability/CriticalPercolation/Modular/RandomTiltedTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/RandomTiltedTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal BigOperators`):
--
--   ```lean
--   lemma OrbitRepresentatives.incoming_finite_ae (R : G.OrbitRepresentatives)
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
--       (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
--       (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y)
--       (N : ℝ≥0∞) (hN : N < ∞) (hb : ∀ ω x, ∑' y, F ω x y ≤ N) (v : V) :
--       ∀ᵐ ω ∂G.law p, (∑' x, F ω x v * G.stabilizerWeight v x) < ∞
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives` and `OAI.CriticalPercolation.BondGraph.stabilizerWeight` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.Aut`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.fullGraph` and `OAI.CriticalPercolation.BondGraph.law` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.expected_weighted_peakRatio`, `OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae` and `OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/RandomTiltedTransport.lean (declaration OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.incoming_finite_ae)

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
variable {V E : Type*} [Countable V] (G : BondGraph V E)

lemma OrbitRepresentatives.incoming_finite_ae (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y)
    (N : ℝ≥0∞) (hN : N < ∞) (hb : ∀ ω x, ∑' y, F ω x y ≤ N) (v : V) :
    ∀ᵐ ω ∂G.law p, (∑' x, F ω x v * G.stabilizerWeight v x) < ∞ := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
