-- Prove2me | Theorems.Thm_OAI_Percolation_infinitely_many_of_pc_lt_lt_pu
-- name    : OAI.Percolation.infinitely_many_of_pc_lt_lt_pu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:45:36.416349+00:00
-- url     : https://prove2.me/theorems/874004aa-3ea0-4b6e-94f4-41db02204af5
-- title:
--   OAI.Percolation.infinitely_many_of_pc_lt_lt_pu: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.infinitely_many_of_pc_lt_lt_pu` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Criticality/Phase.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Criticality/Phase.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem infinitely_many_of_pc_lt_lt_pu [Infinite V]
--       (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
--       (hqt : QuasiTransitive G) (p : unitInterval) (hc : pc G < p) (hu : p < pu G) :
--       ∀ᵐ ω ∂law p, (infiniteClusters G ω).Infinite
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite` and `OAI.Percolation.QuasiTransitive` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.infiniteClusters`, `OAI.Percolation.law`, `OAI.Percolation.pc` and `OAI.Percolation.pu` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.arbitrary_cayley` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Criticality/Phase.lean (declaration OAI.Percolation.infinitely_many_of_pc_lt_lt_pu)

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem infinitely_many_of_pc_lt_lt_pu [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hc : pc G < p) (hu : p < pu G) :
    ∀ᵐ ω ∂law p, (infiniteClusters G ω).Infinite := by
  sorry
end Percolation

end OAI
end
