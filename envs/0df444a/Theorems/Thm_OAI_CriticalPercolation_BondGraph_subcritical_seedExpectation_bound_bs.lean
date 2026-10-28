-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_subcritical_seedExpectation_bound_bs
-- name    : OAI.CriticalPercolation.BondGraph.subcritical_seedExpectation_bound_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:28:44.844227+00:00
-- url     : https://prove2.me/theorems/935b4c3f-7f13-4116-804a-8403642ac4e6
-- title:
--   OAI.CriticalPercolation.BondGraph.subcritical_seedExpectation_bound_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.subcritical_seedExpectation_bound` of [lean/OAI/Probability/CriticalPercolation/ProductMeasure/LayerExpectation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/ProductMeasure/LayerExpectation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical ENNReal BigOperators`, `open BernoulliProduct`):
--
--   ```lean
--   lemma subcritical_seedExpectation_bound_bs [Countable V] [Countable E]
--       (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (q : unitInterval) (hqc : q<G.criticalProbability) (o : V) :
--       ∃ C : ℝ≥0∞, C≠∞ ∧ ∀ D : Set V, G.seedExpectation q D o≤C
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.criticalProbability` and `OAI.CriticalPercolation.BondGraph.seedExpectation` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.nonunimodular_no_percolation_at_criticality_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/ProductMeasure/LayerExpectation.lean (declaration OAI.CriticalPercolation.BondGraph.subcritical_seedExpectation_bound)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma subcritical_seedExpectation_bound_bs [Countable V] [Countable E]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (q : unitInterval) (hqc : q<G.criticalProbability) (o : V) :
    ∃ C : ℝ≥0∞, C≠∞ ∧ ∀ D : Set V, G.seedExpectation q D o≤C := by
  sorry

end BondGraph
end CriticalPercolation
end
end

end OAI
end
