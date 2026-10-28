-- Prove2me | Theorems.Thm_OAI_KaplanskyConsequences_Regular_polynomial_dense_zero
-- name    : OAI.KaplanskyConsequences.Regular.polynomial_dense_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T15:31:26.182731+00:00
-- url     : https://prove2.me/theorems/1716dd45-68a9-480b-a1b6-378cf1d67ad5
-- title:
--   OAI.KaplanskyConsequences.Regular.polynomial_dense_zero: intermediate lemma from OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KaplanskyConsequences.Regular.polynomial_dense_zero` of [lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/ReducedPolynomials.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/ReducedPolynomials.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KaplanskyConsequences.Regular`, with `open scoped BigOperators InnerProductSpace ENNReal`):
--
--   ```lean
--   lemma polynomial_dense_zero (x : Algebra G) (hx : coefficient x = 0)
--       (ε : ℝ) (hε : 0 < ε) :
--       ∃ c : G →₀ ℂ, c 1=0 ∧ ‖x-polynomial c‖ < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.KaplanskyConsequences.Regular.coefficient` and `OAI.KaplanskyConsequences.Regular.polynomial` (definitions bundle `OAIQ15Sf008` of this split); `OAI.KaplanskyConsequences.Regular.Algebra`, `OAI.KaplanskyConsequences.Regular.HilbertSum` and `OAI.KaplanskyConsequences.Regular.instIsClosedContinuousLinearMapComplexIdSubtypePreLpMemAddSubgroupHilbertSumCoeStarSubalgebraAlgebra` (the published bundle `Def_KaplanskyStableFiniteness`).
--
--   **Used by.** The proof of `OAI.KaplanskyConsequences.Regular.algebra_F2_simple` of this split imports it.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/ReducedPolynomials.lean (declaration OAI.KaplanskyConsequences.Regular.polynomial_dense_zero)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

lemma polynomial_dense_zero (x : Algebra G) (hx : coefficient x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : G →₀ ℂ, c 1=0 ∧ ‖x-polynomial c‖ < ε := by
  sorry

end KaplanskyConsequences.Regular

end

end OAI
end
