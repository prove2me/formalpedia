-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_actual_history_success
-- name    : OAI.CommonBasesFPRAS.actual_history_success
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:27:57.593874+00:00
-- url     : https://prove2.me/theorems/ba944e21-3782-468d-b76e-bbb90dc68254
-- title:
--   OAI.CommonBasesFPRAS.actual_history_success: intermediate lemma from OpenAI, Approximate counting of common bases of two matroids
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.common_bases_fpras`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Approximate counting of common bases of two matroids*, OpenAI Math Release, September 23, 2026, result family 114, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CommonBasesFPRAS.actual_history_success` of [lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CommonBasesFPRAS`, with `open scoped RealInnerProductSpace BigOperators Matrix`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem actual_history_success
--       (hN : (10:ℝ)^10*(L+1)*n^14/η^2 ≤ N) :
--       19/20 ≤ FiniteExperiment.expect (phaseKernel n hn M N L) L []
--         (fun h => if SuccessfulHistory GS M n η (observedSets n N) h then 1 else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.ChainIndex`, `OAI.CommonBasesFPRAS.ChainState`, `OAI.CommonBasesFPRAS.PhaseSample`, `OAI.CommonBasesFPRAS.SuccessfulHistory`, `OAI.CommonBasesFPRAS.observedSets`, `OAI.CommonBasesFPRAS.pairedSlots`, `OAI.CommonBasesFPRAS.phaseKernel`, `OAI.CommonBasesFPRAS.FiniteChain.sampleFintype` and `OAI.CommonBasesFPRAS.FiniteExperiment.expect` (definitions bundle `OAIQ2Mt000` of this split).
--
--   **Used by.** The proof of `OAI.CommonBasesFPRAS.rational_algorithm_success` of this split imports it.
-- source:
--   OpenAI, Approximate counting of common bases of two matroids, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 114; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean (declaration OAI.CommonBasesFPRAS.actual_history_success)

import Mathlib
import Definitions.Def_OAIQ2Mt000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open scoped BigOperators Classical

open Set

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
section PhaseSuccess
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
    (hE : M.E=Set.univ) (hR : M.eRank=(n:ℕ∞))
local notation "GS" => pairedSlots n
variable (N L : ℕ) (η : ℝ) (hη0 : 0<η) (hη1 : η ≤ 1/3)
include hE hR hη0 hη1 in

theorem actual_history_success
    (hN : (10:ℝ)^10*(L+1)*n^14/η^2 ≤ N) :
    19/20 ≤ FiniteExperiment.expect (phaseKernel n hn M N L) L []
      (fun h => if SuccessfulHistory GS M n η (observedSets n N) h then 1 else 0) := by
  sorry
end PhaseSuccess
open scoped BigOperators Classical

end

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

end

namespace MachineCode


open Expression

open Expression

open Expression

open Expression

open Expression

open Expression
end MachineCode

end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

end OAI
end
