-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_critical_null_of_action_coordinates_bs
-- name    : OAI.CriticalPercolation.BondGraph.critical_null_of_action_coordinates_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:22:53.427615+00:00
-- url     : https://prove2.me/theorems/c8359c5d-1324-4e8b-bc46-7f310a28ff5e
-- title:
--   OAI.CriticalPercolation.BondGraph.critical_null_of_action_coordinates_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.critical_null_of_action_coordinates` of [lean/OAI/Probability/CriticalPercolation/Classification/StructuredCoordinates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Classification/StructuredCoordinates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory ProbabilityTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   theorem critical_null_of_action_coordinates_bs
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (ha : G.PreservesEnds (Λ := Λ))
--       (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
--       (hg : G.SubexponentialGrowth) (hpc : G.criticalProbability<1)
--       (a : Λ → ℤ×ℤ) (z : V → ℤ×ℤ) (honto : Surjective z)
--       (hz : ∀ g v, z (g • v)=a g+z v)
--       (hnoray : ∀ᵐ ω ∂G.law G.criticalProbability,
--         ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n,
--           |(z (r.vertex n)).1|≤U ∧ |(z (r.vertex n)).2|≤W) :
--       G.law G.criticalProbability G.percolates=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.OpenRay`, `OAI.CriticalPercolation.BondGraph.PreservesEnds`, `OAI.CriticalPercolation.BondGraph.SubexponentialGrowth`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law` and `OAI.CriticalPercolation.BondGraph.percolates` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Classification/StructuredCoordinates.lean (declaration OAI.CriticalPercolation.BondGraph.critical_null_of_action_coordinates)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E Λ N : Type*} (G : BondGraph V E)
  [Group Λ] [Group N] [MulAction Λ V] [MulAction Λ E]

theorem critical_null_of_action_coordinates_bs
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (hg : G.SubexponentialGrowth) (hpc : G.criticalProbability<1)
    (a : Λ → ℤ×ℤ) (z : V → ℤ×ℤ) (honto : Surjective z)
    (hz : ∀ g v, z (g • v)=a g+z v)
    (hnoray : ∀ᵐ ω ∂G.law G.criticalProbability,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n,
        |(z (r.vertex n)).1|≤U ∧ |(z (r.vertex n)).2|≤W) :
    G.law G.criticalProbability G.percolates=0 := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
