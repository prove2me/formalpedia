-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_normalized_peak_surgery_bs
-- name    : OAI.Percolation.BenjaminiSchramm.normalized_peak_surgery_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:39:14.878403+00:00
-- url     : https://prove2.me/theorems/1ed7678a-a599-4e3d-859f-c06538e6db7d
-- title:
--   OAI.Percolation.BenjaminiSchramm.normalized_peak_surgery_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.normalized_peak_surgery` of [lean/OAI/Probability/BenjaminiSchramm/NormalizedPeakSurgery.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/NormalizedPeakSurgery.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open Set MeasureTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   theorem normalized_peak_surgery_bs
--       (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
--       (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
--       (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
--       (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
--       (R : ℝ) (hR : 0 < R)
--       (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
--         |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
--       ∃ L : ℕ, ∀ (p : unitInterval) (d : ℕ), (∀ v, degree G v ≤ d) →
--         ∀ (n : ℕ), 0 < n → ∀ (x : V) (u : ℝ) (S F : Finset V),
--         (lowerFrontierCell G
--           (internalEdges G {v | (criticalModel G).adjustedLayerIndex
--             ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V)).Nonempty →
--         F.Nonempty →
--         law p (lowerFrontierCell G
--           (internalEdges G {v | (criticalModel G).adjustedLayerIndex
--             ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V))*
--           ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(F.card+L+1))) ≤
--         law p (lowerFrontierCell G
--           (internalEdges G {v | (criticalModel G).adjustedLayerIndex
--             ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V) ∩
--           {ω | ∃ z, R*((n : ℝ)+1) < (criticalModel G).orbitAdjustedHeight
--               ((criticalModel G).stationaryOrbitWeight μ) x z ∧
--             (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ≤ R*((n : ℝ)+4) ∧
--             ω ∈ strictHeightPeakConnection G
--               ((criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x) x z})
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.internalEdges`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.VertexOrbit`, `OAI.CriticalPercolation.BondGraph.adjustedLayerIndex`, `OAI.CriticalPercolation.BondGraph.orbitAdjustedHeight`, `OAI.CriticalPercolation.BondGraph.orbitWalkKernel`, `OAI.CriticalPercolation.BondGraph.stationaryOrbitWeight` and `OAI.Percolation.BenjaminiSchramm.strictHeightPeakConnection` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.orbitChainStep` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.degree`, `OAI.Percolation.BenjaminiSchramm.criticalModel` and `OAI.Percolation.BenjaminiSchramm.lowerFrontierCell` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive` and `OAI.Percolation.law` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.subcritical_peak_band_probability_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/NormalizedPeakSurgery.lean (declaration OAI.Percolation.BenjaminiSchramm.normalized_peak_surgery)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem normalized_peak_surgery_bs
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ L : ℕ, ∀ (p : unitInterval) (d : ℕ), (∀ v, degree G v ≤ d) →
      ∀ (n : ℕ), 0 < n → ∀ (x : V) (u : ℝ) (S F : Finset V),
      (lowerFrontierCell G
        (internalEdges G {v | (criticalModel G).adjustedLayerIndex
          ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V)).Nonempty →
      F.Nonempty →
      law p (lowerFrontierCell G
        (internalEdges G {v | (criticalModel G).adjustedLayerIndex
          ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V))*
        ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(F.card+L+1))) ≤
      law p (lowerFrontierCell G
        (internalEdges G {v | (criticalModel G).adjustedLayerIndex
          ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V) ∩
        {ω | ∃ z, R*((n : ℝ)+1) < (criticalModel G).orbitAdjustedHeight
            ((criticalModel G).stationaryOrbitWeight μ) x z ∧
          (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ≤ R*((n : ℝ)+4) ∧
          ω ∈ strictHeightPeakConnection G
            ((criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x) x z}) := by
  sorry

end Percolation.BenjaminiSchramm

end

end OAI
end
