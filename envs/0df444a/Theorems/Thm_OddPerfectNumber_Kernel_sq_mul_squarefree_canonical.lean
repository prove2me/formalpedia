-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sq_mul_squarefree_canonical
-- name    : OddPerfectNumber.Kernel.sq_mul_squarefree_canonical
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T09:21:59.534188+00:00
-- url     : https://prove2.me/theorems/be26a1fa-1671-4fd6-8e1d-d19ed80f5742
-- title:
--   Every positive natural is a square times a square-free number
-- statement:
--   Every positive natural number $s$ factors as $s = d_1^2 d_2$ with $d_2$ square-free and both factors positive. This is the standard square-free decomposition, and it is the missing bridge between the Dris index $s$ and the square-free-cardinality machinery already proved for this workstream. Concretely the proved children `OddPerfectNumber.Kernel.squarefree_card_ge_three_of_not_small` (64627c09-9af1-4ab3-afc0-a3498abf1dc3), `OddPerfectNumber.Kernel.squarefree_card_ge_two_of_not_one_or_prime` (9c90129e-60c2-4fa1-aa32-c55ece1e485d) and `OddPerfectNumber.Kernel.squarefree_card_two_eq_two_primes` (04aeb617-292f-4f96-ba00-ac391f0a5fa8) are all stated for the square-free number itself, and the open child `OddPerfectNumber.Kernel.five_index_not_prime_mul_square` (2ec27119-2f77-425b-ab15-a95e11c2f9bc) rules out $s = q a^2$ for $q$ prime, which is precisely the statement that the square-free part $d_2$ is not prime. The $k = 5$ reduction to the bound $\omega(\mathrm{squarefree\_part}(s)) \ge 3$ therefore needs exactly this decomposition and no more. The pinned Mathlib revision already supplies it as `Nat.sq_mul_squarefree_of_pos (hn : 0 < n) : ∃ a b, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a` at `Mathlib/Data/Nat/Squarefree.lean:306`, which already has the square on the left, so this child is pure reorientation with $d_1 := b$ and $d_2 := a$ and no commutativity argument at all.
-- source:
--   Mathlib only. `Nat.sq_mul_squarefree_of_pos` at `Mathlib/Data/Nat/Squarefree.lean:306` in the pinned revision `0df444a360eaa60ab8c11dca51a86af692955474` has exactly the type `{n : ℕ} → (0 < n) → ∃ a b, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a`. The product is already ordered square-first, so the witness is transported with `d1 := b`, `d2 := a` and the equation is used verbatim, with no commutativity rewriting. No conjecture-specific content and no deep input. Isolating it keeps the natural-number cancellation out of the k=5 wrapper and makes explicit that the standard square-free decomposition is all that is being used.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sq_mul_squarefree_canonical (s : Nat) (hspos : 0 < s) :
    ∃ d1 d2 : Nat, 0 < d1 ∧ 0 < d2 ∧ d1 ^ 2 * d2 = s ∧ Squarefree d2 := by
  sorry

end OddPerfectNumber.Kernel
