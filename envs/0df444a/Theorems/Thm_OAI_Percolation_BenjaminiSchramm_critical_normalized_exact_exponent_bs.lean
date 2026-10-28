-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_normalized_exact_exponent_bs
-- name    : OAI.Percolation.BenjaminiSchramm.critical_normalized_exact_exponent_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:37:24.616453+00:00
-- url     : https://prove2.me/theorems/2c0bd54c-9f75-414a-99f3-d10a5fbd7ef8
-- title:
--   OAI.Percolation.BenjaminiSchramm.critical_normalized_exact_exponent_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.critical_normalized_exact_exponent` of [lean/OAI/Probability/BenjaminiSchramm/NormalizedExponentComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/NormalizedExponentComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open Set MeasureTheory Filter`, `open scoped Classical ENNReal Topology`):
--
--   ```lean
--   theorem critical_normalized_exact_exponent_bs
--       (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
--       (hu : ¬ (criticalModel G).CombinatoriallyUnimodular)
--       (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
--       (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ = μ) :
--       ∃ α : ℝ, 1 ≤ α ∧
--         (∀ t : ℝ, 0 ≤ t → ((criticalModel G).infimalAdjustedCrossing
--           ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t)) ∧
--         (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
--           c*Real.exp (-(α+ε)*n) ≤ ((criticalModel G).infimalAdjustedCrossing
--             ((criticalModel G).stationaryOrbitWeight μ) (pc G) n).toReal) ∧
--         Tendsto (fun n : ℕ => -Real.log ((criticalModel G).infimalAdjustedCrossing
--           ((criticalModel G).stationaryOrbitWeight μ) (pc G) n).toReal/n) atTop (𝓝 α)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.VertexOrbit`, `OAI.CriticalPercolation.BondGraph.infimalAdjustedCrossing`, `OAI.CriticalPercolation.BondGraph.orbitWalkKernel` and `OAI.CriticalPercolation.BondGraph.stationaryOrbitWeight` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.orbitChainStep` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.BenjaminiSchramm.criticalModel` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_lower_slab_fractional_profile_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/NormalizedExponentComparison.lean (declaration OAI.Percolation.BenjaminiSchramm.critical_normalized_exact_exponent)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace Percolation.BenjaminiSchramm

variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_normalized_exact_exponent_bs
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hu : ¬ (criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ = μ) :
    ∃ α : ℝ, 1 ≤ α ∧
      (∀ t : ℝ, 0 ≤ t → ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
        c*Real.exp (-(α+ε)*n) ≤ ((criticalModel G).infimalAdjustedCrossing
          ((criticalModel G).stationaryOrbitWeight μ) (pc G) n).toReal) ∧
      Tendsto (fun n : ℕ => -Real.log ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) n).toReal/n) atTop (𝓝 α) := by
  sorry

end Percolation.BenjaminiSchramm

end

end OAI
end
