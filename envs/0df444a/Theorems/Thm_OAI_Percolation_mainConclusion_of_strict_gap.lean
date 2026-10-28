-- Prove2me | Theorems.Thm_OAI_Percolation_mainConclusion_of_strict_gap
-- name    : OAI.Percolation.mainConclusion_of_strict_gap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:44:37.540543+00:00
-- url     : https://prove2.me/theorems/32af5513-ed4a-4ff6-b915-e93a9570a3c9
-- title:
--   OAI.Percolation.mainConclusion_of_strict_gap: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.mainConclusion_of_strict_gap` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Graph/Paths.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Graph/Paths.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem mainConclusion_of_strict_gap [Infinite V] (G : BondGraph V E)
--       (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
--       (hgap : pc G < ptwo G) : MainConclusion G
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.MainConclusion` and `OAI.Percolation.QuasiTransitive` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.pc` and `OAI.Percolation.ptwo` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.arbitrary_cayley` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Graph/Paths.lean (declaration OAI.Percolation.mainConclusion_of_strict_gap)

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

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MainBridge
attribute [local instance] Classical.propDecidable

theorem mainConclusion_of_strict_gap [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hgap : pc G < ptwo G) : MainConclusion G := by
  sorry

end MainBridge

end Percolation

end OAI
end
