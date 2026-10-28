-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_subcritical_weighted_peak_conditional_layers_bs
-- name    : OAI.Percolation.BenjaminiSchramm.subcritical_weighted_peak_conditional_layers_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:39:57.053594+00:00
-- url     : https://prove2.me/theorems/54e43565-9d95-4cc8-b2c6-4baed0fe6239
-- title:
--   OAI.Percolation.BenjaminiSchramm.subcritical_weighted_peak_conditional_layers_bs (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.subcritical_weighted_peak_conditional_layers` of [lean/OAI/Probability/BenjaminiSchramm/SubcriticalPeakConditional.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/SubcriticalPeakConditional.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open Set MeasureTheory`, `open scoped Classical ENNReal BigOperators`):
--
--   ```lean
--   theorem subcritical_weighted_peak_conditional_layers_bs
--       (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
--       (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
--       (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
--       (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
--       (R : ℝ) (hR : 0 < R)
--       (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
--         |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
--       (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < pc G)
--       (O : (criticalModel G).OrbitRepresentatives) :
--       ∃ β : ℝ, R < β ∧ ∃ K : ℝ, 0 < K ∧
--         (∀ n : ℕ, (criticalModel G).supAdjustedUpLayerMoment
--           ((criticalModel G).stationaryOrbitWeight μ) R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) ∧
--         ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
--           ENNReal.ofReal (c*Real.exp (-(β-R)*n)) ≤
--             (criticalModel G).peakSurvivalProbability O ((criticalModel G).stationaryOrbitWeight μ) R p n ∧
--           ∀ l : ℕ, (criticalModel G).peakSurvivalLayerMoment O
--             ((criticalModel G).stationaryOrbitWeight μ) R p n l ≤
--             (criticalModel G).peakSurvivalProbability O ((criticalModel G).stationaryOrbitWeight μ) R p n *
--               ENNReal.ofReal (C*Real.exp (-(β-R)*max ((l : ℝ)-n) 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives`, `OAI.CriticalPercolation.BondGraph.VertexOrbit`, `OAI.CriticalPercolation.BondGraph.orbitAdjustedHeight`, `OAI.CriticalPercolation.BondGraph.orbitWalkKernel`, `OAI.CriticalPercolation.BondGraph.peakSurvivalLayerMoment`, `OAI.CriticalPercolation.BondGraph.peakSurvivalProbability`, `OAI.CriticalPercolation.BondGraph.stationaryOrbitWeight` and `OAI.CriticalPercolation.BondGraph.supAdjustedUpLayerMoment` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.orbitChainStep` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.BenjaminiSchramm.criticalModel` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_lower_slab_fractional_profile_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/SubcriticalPeakConditional.lean (declaration OAI.Percolation.BenjaminiSchramm.subcritical_weighted_peak_conditional_layers)

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
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem subcritical_weighted_peak_conditional_layers_bs
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < pc G)
    (O : (criticalModel G).OrbitRepresentatives) :
    ∃ β : ℝ, R < β ∧ ∃ K : ℝ, 0 < K ∧
      (∀ n : ℕ, (criticalModel G).supAdjustedUpLayerMoment
        ((criticalModel G).stationaryOrbitWeight μ) R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
        ENNReal.ofReal (c*Real.exp (-(β-R)*n)) ≤
          (criticalModel G).peakSurvivalProbability O ((criticalModel G).stationaryOrbitWeight μ) R p n ∧
        ∀ l : ℕ, (criticalModel G).peakSurvivalLayerMoment O
          ((criticalModel G).stationaryOrbitWeight μ) R p n l ≤
          (criticalModel G).peakSurvivalProbability O ((criticalModel G).stationaryOrbitWeight μ) R p n *
            ENNReal.ofReal (C*Real.exp (-(β-R)*max ((l : ℝ)-n) 0)) := by
  sorry

end Percolation.BenjaminiSchramm

end

end OAI
end
