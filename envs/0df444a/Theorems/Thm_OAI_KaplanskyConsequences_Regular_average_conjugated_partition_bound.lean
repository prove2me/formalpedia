-- Prove2me | Theorems.Thm_OAI_KaplanskyConsequences_Regular_average_conjugated_partition_bound
-- name    : OAI.KaplanskyConsequences.Regular.average_conjugated_partition_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T15:30:00.363879+00:00
-- url     : https://prove2.me/theorems/644c7fe5-b746-4861-bf8f-4a9989ace569
-- title:
--   OAI.KaplanskyConsequences.Regular.average_conjugated_partition_bound (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KaplanskyConsequences.Regular.average_conjugated_partition_bound` of [lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/PowersAverageBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/PowersAverageBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KaplanskyConsequences.Regular`, with `open scoped BigOperators InnerProductSpace ENNReal`):
--
--   ```lean
--   lemma average_conjugated_partition_bound {N : ℕ} (D : G → Prop) (h : Fin N → G)
--       (hd : ∀ i j w, ¬D ((h i)⁻¹*w) → ¬D ((h j)⁻¹*w) → i=j)
--       (u : G) (x : Algebra G) (hT : mask D*(conjugateMap u x).val*mask D=0) :
--       ‖averageConjugate (fun i => h i*u) x‖ ≤ (N:ℝ)⁻¹*(2*Real.sqrt N*‖x‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KaplanskyConsequences.Regular.mask` (definitions bundle `OAIQ15Sf004` of this split); `OAI.KaplanskyConsequences.Regular.averageConjugate` and `OAI.KaplanskyConsequences.Regular.conjugateMap` (definitions bundle `OAIQ15Sf008` of this split); `OAI.KaplanskyConsequences.Regular.Algebra`, `OAI.KaplanskyConsequences.Regular.HilbertSum` and `OAI.KaplanskyConsequences.Regular.instIsClosedContinuousLinearMapComplexIdSubtypePreLpMemAddSubgroupHilbertSumCoeStarSubalgebraAlgebra` (the published bundle `Def_KaplanskyStableFiniteness`).
--
--   **Used by.** The proof of `OAI.KaplanskyConsequences.Regular.polynomial_average_small` of this split imports it.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/PowersAverageBound.lean (declaration OAI.KaplanskyConsequences.Regular.average_conjugated_partition_bound)

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

lemma average_conjugated_partition_bound {N : ℕ} (D : G → Prop) (h : Fin N → G)
    (hd : ∀ i j w, ¬D ((h i)⁻¹*w) → ¬D ((h j)⁻¹*w) → i=j)
    (u : G) (x : Algebra G) (hT : mask D*(conjugateMap u x).val*mask D=0) :
    ‖averageConjugate (fun i => h i*u) x‖ ≤ (N:ℝ)⁻¹*(2*Real.sqrt N*‖x‖) := by
  sorry

end KaplanskyConsequences.Regular

end

end OAI
end
