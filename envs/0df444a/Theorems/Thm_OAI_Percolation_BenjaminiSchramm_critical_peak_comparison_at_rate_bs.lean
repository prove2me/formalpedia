-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_peak_comparison_at_rate_bs
-- name    : OAI.Percolation.BenjaminiSchramm.critical_peak_comparison_at_rate_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:37:48.960795+00:00
-- url     : https://prove2.me/theorems/eb9bcfb7-0695-4c53-93e7-cc10b84b0b62
-- title:
--   OAI.Percolation.BenjaminiSchramm.critical_peak_comparison_at_rate_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.critical_peak_comparison_at_rate` of [lean/OAI/Probability/BenjaminiSchramm/CriticalPeakComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/CriticalPeakComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open Set MeasureTheory`, `open scoped Classical ENNReal BigOperators`):
--
--   ```lean
--   theorem critical_peak_comparison_at_rate_bs
--       (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
--       (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
--       (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
--       (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
--       (α : ℝ) (hcross : ∀ t : ℝ, 0 ≤ t →
--         ((criticalModel G).infimalAdjustedCrossing
--           ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t))
--       (R : ℝ) (hR : 0 < R)
--       (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
--         |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
--       ∃ M : ℝ, 0 < M ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧ ∃ L : ℝ, 0 < L ∧
--         ∀ k, 0 ≤ k → ∀ r, 0 ≤ r → ∀ ell, 0 < ell → ∀ v₀,
--         (criticalModel G).fullPeakDownProbability
--           ((criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hq))
--           ((criticalModel G).stationaryOrbitWeight μ) (pc G) ell*
--         (criticalModel G).mixedHeightLayerMoment ((criticalModel G).stationaryOrbitWeight μ)
--           (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
--             K*ENNReal.ofReal (Real.exp (L*r-(α-1)*(ell+k)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.VertexOrbit`, `OAI.CriticalPercolation.BondGraph.fullPeakDownProbability`, `OAI.CriticalPercolation.BondGraph.infimalAdjustedCrossing`, `OAI.CriticalPercolation.BondGraph.mixedHeightLayerMoment`, `OAI.CriticalPercolation.BondGraph.orbitAdjustedHeight`, `OAI.CriticalPercolation.BondGraph.orbitRepresentatives`, `OAI.CriticalPercolation.BondGraph.orbitWalkKernel` and `OAI.CriticalPercolation.BondGraph.stationaryOrbitWeight` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.orbitChainStep` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.BenjaminiSchramm.criticalModel` and `OAI.Percolation.BenjaminiSchramm.criticalModel_quasiTransitive` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_slab_fractional_of_peak_survival_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/CriticalPeakComparison.lean (declaration OAI.Percolation.BenjaminiSchramm.critical_peak_comparison_at_rate)

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
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_peak_comparison_at_rate_bs
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ) (hcross : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t))
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ M : ℝ, 0 < M ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧ ∃ L : ℝ, 0 < L ∧
      ∀ k, 0 ≤ k → ∀ r, 0 ≤ r → ∀ ell, 0 < ell → ∀ v₀,
      (criticalModel G).fullPeakDownProbability
        ((criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hq))
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) ell*
      (criticalModel G).mixedHeightLayerMoment ((criticalModel G).stationaryOrbitWeight μ)
        (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
          K*ENNReal.ofReal (Real.exp (L*r-(α-1)*(ell+k))) := by
  sorry

end Percolation.BenjaminiSchramm

end

end OAI
end
