-- Prove2me | Theorems.Thm_OAI_Percolation_critical_unique_probability_zero
-- name    : OAI.Percolation.critical_unique_probability_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:50:48.705423+00:00
-- url     : https://prove2.me/theorems/8a49dbc6-e6c2-4cfc-837e-e5727a3e1945
-- title:
--   OAI.Percolation.critical_unique_probability_zero: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.critical_unique_probability_zero` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Criticality/ClusterCount.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Criticality/ClusterCount.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem critical_unique_probability_zero [Infinite V] (G : BondGraph V E)
--       (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
--       (hh : 0 < hV G) : law (pc G) {ω | ∃! C, C ∈ infiniteClusters G ω} = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite` and `OAI.Percolation.QuasiTransitive` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.hV` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.infiniteClusters`, `OAI.Percolation.law` and `OAI.Percolation.pc` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.critical_finite_ae_of_transport` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Criticality/ClusterCount.lean (declaration OAI.Percolation.critical_unique_probability_zero)

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
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem critical_unique_probability_zero [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) : law (pc G) {ω | ∃! C, C ∈ infiniteClusters G ω} = 0 := by
  sorry

end Percolation

end OAI
end
