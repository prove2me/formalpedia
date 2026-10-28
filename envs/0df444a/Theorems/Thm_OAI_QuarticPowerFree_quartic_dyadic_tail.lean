-- Prove2me | Theorems.Thm_OAI_QuarticPowerFree_quartic_dyadic_tail
-- name    : OAI.QuarticPowerFree.quartic_dyadic_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T15:06:32.695525+00:00
-- url     : https://prove2.me/theorems/0fde891a-7643-455b-a959-0a626fd1ef6a
-- title:
--   OAI.QuarticPowerFree.quartic_dyadic_tail: intermediate lemma from OpenAI, Squarefree values of quartics and power-free values of polynomials
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.QuarticPowerFree.allDegrees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Squarefree values of quartics and power-free values of polynomials*, OpenAI Math Release, September 24, 2026, result family 20, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.QuarticPowerFree.quartic_dyadic_tail` of [lean/OAI/NumberTheory/PowerFree/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.QuarticPowerFree`, with `open Filter NumberField`, `open scoped Topology Classical BigOperators`):
--
--   ```lean
--   theorem quartic_dyadic_tail (f : Polynomial ℤ) (hf : f.IsPrimitive)
--       (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hc : 0 < f.leadingCoeff)
--       (hd : f.natDegree=4) :
--       ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
--         (dyadicTailCount f (f.natDegree-2) N:ℝ) ≤ C*(N:ℝ)^(1-3/1000:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.QuarticPowerFree.dyadicTailCount` (definitions bundle `OAIB3Qp000` of this split).
--
--   **Used by.** The proof of `OAI.QuarticPowerFree.allDegrees` of this split imports it.
-- source:
--   OpenAI, Squarefree values of quartics and power-free values of polynomials, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 20; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/manuscript.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/Main.lean (declaration OAI.QuarticPowerFree.quartic_dyadic_tail)

import Mathlib
import Definitions.Def_OAIB3Qp000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open Filter NumberField
open scoped Topology Classical BigOperators

theorem quartic_dyadic_tail (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hc : 0 < f.leadingCoeff)
    (hd : f.natDegree=4) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (dyadicTailCount f (f.natDegree-2) N:ℝ) ≤ C*(N:ℝ)^(1-3/1000:ℝ) := by
  sorry

end

end QuarticPowerFree

end OAI
end
