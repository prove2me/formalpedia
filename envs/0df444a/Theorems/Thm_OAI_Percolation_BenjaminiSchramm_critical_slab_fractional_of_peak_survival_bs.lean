-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_slab_fractional_of_peak_survival_bs
-- name    : OAI.Percolation.BenjaminiSchramm.critical_slab_fractional_of_peak_survival_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:38:20.554823+00:00
-- url     : https://prove2.me/theorems/c3b8a135-0d8f-4603-a2e1-0d7f3f842de8
-- title:
--   OAI.Percolation.BenjaminiSchramm.critical_slab_fractional_of_peak_survival_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.critical_slab_fractional_of_peak_survival` of [lean/OAI/Probability/BenjaminiSchramm/CriticalFractionalSlab.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/CriticalFractionalSlab.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open Set MeasureTheory`, `open scoped Classical ENNReal BigOperators`):
--
--   ```lean
--   theorem critical_slab_fractional_of_peak_survival_bs
--       (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
--       (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
--       (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
--       (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
--       (α : ℝ) (hα : 1 ≤ α) (hcross : ∀ t : ℝ, 0 ≤ t →
--         ((criticalModel G).infimalAdjustedCrossing
--           ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t))
--       (R : ℝ) (hR : 0 < R)
--       (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
--         |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
--       (hsurv : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ ell : ℝ, 0 < ell →
--         ENNReal.ofReal (c*Real.exp (-((α-1)+ε)*ell)) ≤
--           (criticalModel G).fullPeakDownProbability
--             ((criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hq))
--             ((criticalModel G).stationaryOrbitWeight μ) (pc G) ell) :
--       ∃ L : ℝ, 0 < L ∧ ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
--         ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
--           (∫⁻ ω, (restrictedLayerCount G
--             (internalEdges G {z | -k-r ≤ (criticalModel G).orbitAdjustedHeight
--               ((criticalModel G).stationaryOrbitWeight μ) x z ∧
--                 (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ≤ 0})
--             {z | -k-R ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ∧
--               (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ≤ -k+R}
--             ω x)^q ∂law (pc G)) ≤ C*ENNReal.ofReal (Real.exp (ζ*k+L*r))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.internalEdges`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.VertexOrbit`, `OAI.CriticalPercolation.BondGraph.fullPeakDownProbability`, `OAI.CriticalPercolation.BondGraph.infimalAdjustedCrossing`, `OAI.CriticalPercolation.BondGraph.orbitAdjustedHeight`, `OAI.CriticalPercolation.BondGraph.orbitRepresentatives`, `OAI.CriticalPercolation.BondGraph.orbitWalkKernel`, `OAI.CriticalPercolation.BondGraph.stationaryOrbitWeight` and `OAI.Percolation.BenjaminiSchramm.restrictedLayerCount` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.orbitChainStep` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.BenjaminiSchramm.criticalModel` and `OAI.Percolation.BenjaminiSchramm.criticalModel_quasiTransitive` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.law` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_lower_slab_fractional_profile_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/CriticalFractionalSlab.lean (declaration OAI.Percolation.BenjaminiSchramm.critical_slab_fractional_of_peak_survival)

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

theorem critical_slab_fractional_of_peak_survival_bs
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ) (hα : 1 ≤ α) (hcross : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t))
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (hsurv : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ ell : ℝ, 0 < ell →
      ENNReal.ofReal (c*Real.exp (-((α-1)+ε)*ell)) ≤
        (criticalModel G).fullPeakDownProbability
          ((criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hq))
          ((criticalModel G).stationaryOrbitWeight μ) (pc G) ell) :
    ∃ L : ℝ, 0 < L ∧ ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
        (∫⁻ ω, (restrictedLayerCount G
          (internalEdges G {z | -k-r ≤ (criticalModel G).orbitAdjustedHeight
            ((criticalModel G).stationaryOrbitWeight μ) x z ∧
              (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ≤ 0})
          {z | -k-R ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ∧
            (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ≤ -k+R}
          ω x)^q ∂law (pc G)) ≤ C*ENNReal.ofReal (Real.exp (ζ*k+L*r)) := by
  sorry

end Percolation.BenjaminiSchramm

end

end OAI
end
