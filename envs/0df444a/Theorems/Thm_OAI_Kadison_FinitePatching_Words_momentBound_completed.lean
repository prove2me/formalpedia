-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_Words_momentBound_completed
-- name    : OAI.Kadison.FinitePatching.Words.momentBound_completed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:57:50.810768+00:00
-- url     : https://prove2.me/theorems/06896b50-81da-4252-8b1b-749e52ce871a
-- title:
--   OAI.Kadison.FinitePatching.Words.momentBound_completed: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching.Words`, with `open scoped ComplexOrder`):
--
--   ```lean
--   lemma momentBound_completed (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
--       (v : PartialUnitary A) {N : ℕ} {B C : ℝ}
--       (hB : MomentBound τ x k v N B)
--       (hpower : ∀ i,((k i).natAbs:ℝ)+2 ≤ C)
--       (hword : ∀ l : List (Letter J K),l.length ≤ N → (wordCost k l:ℝ) ≤ C) :
--       MomentBound τ x k v.completed N (B+C*Real.sqrt (1-(τ v.support).re))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FinitePatching.PartialUnitary` (definitions bundle `OAIQ039C009` of this split); `OAI.Kadison.FinitePatching.Words.Letter` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FinitePatching.PartialUnitary.completed` and `OAI.Kadison.FinitePatching.Words.MomentBound` (definitions bundle `OAIQ039C035` of this split); `OAI.Kadison.FinitePatching.Words.wordCost` (definitions bundle `OAIQ039C045` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.exists_full_unitary_finite_tests` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C045

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

include hτ in
lemma momentBound_completed (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
    (v : PartialUnitary A) {N : ℕ} {B C : ℝ}
    (hB : MomentBound τ x k v N B)
    (hpower : ∀ i,((k i).natAbs:ℝ)+2 ≤ C)
    (hword : ∀ l : List (Letter J K),l.length ≤ N → (wordCost k l:ℝ) ≤ C) :
    MomentBound τ x k v.completed N (B+C*Real.sqrt (1-(τ v.support).re)) := by
  sorry

end Kadison.FinitePatching.Words

end

end
end

end OAI
end
