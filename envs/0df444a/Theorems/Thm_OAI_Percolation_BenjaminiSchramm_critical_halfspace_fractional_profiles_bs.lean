-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_halfspace_fractional_profiles_bs
-- name    : OAI.Percolation.BenjaminiSchramm.critical_halfspace_fractional_profiles_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:38:03.760201+00:00
-- url     : https://prove2.me/theorems/75df4fc5-67ad-4e34-bd65-909eceafe3bc
-- title:
--   OAI.Percolation.BenjaminiSchramm.critical_halfspace_fractional_profiles_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.critical_halfspace_fractional_profiles` of [lean/OAI/Probability/BenjaminiSchramm/CriticalHalfspaceProfiles.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/CriticalHalfspaceProfiles.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open Set MeasureTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   theorem critical_halfspace_fractional_profiles_bs
--       (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
--       (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
--       (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
--       (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
--       (R : ℝ) (hR : 0 < R)
--       (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
--         |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
--       ∀ q : ℝ, 0 < q → q < 1 →
--         (criticalModel G).downwardHalfspaceFractionalProfile
--           ((criticalModel G).stationaryOrbitWeight μ) (pc G) R q ∧
--         (criticalModel G).upwardHalfspaceFractionalProfile
--           ((criticalModel G).stationaryOrbitWeight μ) (pc G) R q
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.VertexOrbit`, `OAI.CriticalPercolation.BondGraph.downwardHalfspaceFractionalProfile`, `OAI.CriticalPercolation.BondGraph.orbitAdjustedHeight`, `OAI.CriticalPercolation.BondGraph.orbitWalkKernel`, `OAI.CriticalPercolation.BondGraph.stationaryOrbitWeight` and `OAI.CriticalPercolation.BondGraph.upwardHalfspaceFractionalProfile` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.orbitChainStep` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.BenjaminiSchramm.criticalModel` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proofs of `OAI.Percolation.BenjaminiSchramm.critical_endpoint_fractional_profiles_bs` and `OAI.Percolation.BenjaminiSchramm.critical_fullspace_threeQuarter_profiles_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/CriticalHalfspaceProfiles.lean (declaration OAI.Percolation.BenjaminiSchramm.critical_halfspace_fractional_profiles)

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
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_halfspace_fractional_profiles_bs
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∀ q : ℝ, 0 < q → q < 1 →
      (criticalModel G).downwardHalfspaceFractionalProfile
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) R q ∧
      (criticalModel G).upwardHalfspaceFractionalProfile
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) R q := by
  sorry

end Percolation.BenjaminiSchramm

end

end OAI
end
