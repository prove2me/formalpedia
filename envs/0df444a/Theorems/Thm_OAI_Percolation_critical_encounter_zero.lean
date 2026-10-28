-- Prove2me | Theorems.Thm_OAI_Percolation_critical_encounter_zero
-- name    : OAI.Percolation.critical_encounter_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:49:41.370134+00:00
-- url     : https://prove2.me/theorems/bca92d7e-29a5-4c12-8860-decff9ab6701
-- title:
--   OAI.Percolation.critical_encounter_zero: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.critical_encounter_zero` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Encounter/ZeroIntensity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Encounter/ZeroIntensity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory SimpleGraph Filter Topology`, `open scoped ENNReal`):
--
--   ```lean
--   theorem critical_encounter_zero
--       (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
--       (hp : 0 < pc G) (root : ι → V) (weight : ι → ℝ)
--       (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
--       (hw1 : ∑ i, weight i = 1)
--       (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) (x : V) :
--       law (pc G) {ω | IsEncounter G ω x} = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.Connected`, `OAI.Percolation.IsEncounter`, `OAI.Percolation.LocallyFinite` and `OAI.Percolation.RootTransport` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.vertexAut` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.law` and `OAI.Percolation.pc` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.critical_finite_ae_of_transport` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Encounter/ZeroIntensity.lean (declaration OAI.Percolation.critical_encounter_zero)

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph Filter Topology
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Fintype ι]

theorem critical_encounter_zero
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hp : 0 < pc G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) (x : V) :
    law (pc G) {ω | IsEncounter G ω x} = 0 := by
  sorry

end Percolation

end OAI
end
