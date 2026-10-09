-- Prove2me | Theorems.Thm_OAI_Erdos3_residue_function_alphabet_card_le_exp
-- name    : OAI.Erdos3.residue_function_alphabet_card_le_exp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:59:43.125175+00:00
-- url     : https://prove2.me/theorems/632ef2d6-dece-41b9-b110-fde372e90beb
-- title:
--   The number of functions from I to Z/q is at most exp(|I| B) when q is at most e^B
-- statement:
--   Let $I$ be a finite type, $q$ a nonzero natural number, and $B$ a real number with $q \le e^{B}$. Then the number of functions $I \to \mathbb{Z}/q$ is at most $\exp(|I| \cdot B)$.
--
--   Lean: `OAI.Erdos3.residue_function_alphabet_card_le_exp` in `lean/OAI/Combinatorics/Progressions/Lattices/RetainedPhysicalCRT.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/RetainedPhysicalCRT.lean#L154

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem residue_function_alphabet_card_le_exp {I : Type*} [Fintype I] {q : ℕ} [NeZero q]
    {B : ℝ} (hq : (q : ℝ) ≤ Real.exp B) :
    (Fintype.card (I → ZMod q) : ℝ) ≤ Real.exp ((Fintype.card I : ℝ) * B) := by
  sorry

end Erdos3
end
end OAI
