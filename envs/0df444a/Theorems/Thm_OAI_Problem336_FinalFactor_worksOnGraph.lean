-- Prove2me | Theorems.Thm_OAI_Problem336_FinalFactor_worksOnGraph
-- name    : OAI.Problem336.FinalFactor.worksOnGraph
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:39:24.667046+00:00
-- url     : https://prove2.me/theorems/0bfbd28c-d7fc-41ac-ae3c-ed0cd607dabe
-- title:
--   OAI.Problem336.FinalFactor.worksOnGraph: intermediate lemma from OpenAI, The free uniform spanning forest is a factor of IID
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem336.fusf_is_factor_iid`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The free uniform spanning forest is a factor of IID*, OpenAI Math Release, September 25, 2026, result family 231, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem336.FinalFactor.worksOnGraph` of [lean/OAI/Probability/SpanningForest/SpanningForest/FinalFactor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SpanningForest/SpanningForest/FinalFactor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem336.FinalFactor`, with `open MeasureTheory ProbabilityTheory`):
--
--   ```lean
--   theorem worksOnGraph (G : GraphCode) : WorksOnGraph rule G
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem336.FinalFactor.rule` (definitions bundle `OAIS336000` of this split); `OAI.Problem336.GraphCode` and `OAI.Problem336.WorksOnGraph` (the published bundle `Def_FreeUniformSpanningForest`).
--
--   **Used by.** The proof of `OAI.Problem336.fusf_is_factor_iid` of this split imports it.
-- source:
--   OpenAI, The free uniform spanning forest is a factor of IID, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 231; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SpanningForest/SpanningForest/FinalFactor.lean (declaration OAI.Problem336.FinalFactor.worksOnGraph)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Definitions.Def_FreeUniformSpanningForest
import Definitions.Def_OAIS336000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.FinalFactor

theorem worksOnGraph (G : GraphCode) : WorksOnGraph rule G := by
  sorry

end Problem336.FinalFactor

end

end OAI
end
