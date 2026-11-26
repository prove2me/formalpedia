-- Prove2me | Theorems.Thm_LefebvreVariations_giuga_conjecture_of_le_600
-- name    : LefebvreVariations.giuga_conjecture_of_le_600
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:03:03.928203+00:00
-- url     : https://prove2.me/theorems/1498c1bf-9859-4a99-8234-395dfb56f4bc
-- title:
--   Lefebvre's variations, No. 44 — on a theme by Giuga: Giuga's criterion for primality holds for 2 <= n <= 600
-- statement:
--   Let $n$ be an integer with $2\le n\le 600$. Then
--   $$ n \text{ is prime} \iff \sum_{k=1}^{n-1} k^{\,n-1}\equiv -1 \pmod n .$$
--
--   This is Giuga's conjecture restricted to $n\le 600$. The forward direction holds for every $n$ by Fermat's little theorem; the content is that no composite $n\le 600$ satisfies the congruence. A composite counterexample for general $n$ would be simultaneously a Carmichael number and a Giuga number and is known to have thousands of digits.
--
--   **Formalization Note** The sum is computed in `ZMod n` over `Finset.Icc 1 (n - 1)` with exponent `n - 1`, exactly as in the parent `giuga_conjecture`; the only addition is the hypothesis `n ≤ 600`. For $n=2$ the sum is $1=-1$ in `ZMod 2`, consistent with $2$ being prime. No junk value occurs since $n\ge 2$.
--
--   **Why this is a variation.** This is a variation of the open platform problem giuga_conjecture (Giuga's conjecture). It is the conjecture played at its first non-trivial size: the complete finite range 2 <= n <= 600, stated in the parent's own definitions (ZMod n power sum). A prover who settles it exhibits exactly the finite computation, in the parent's own formalization, that any counterexample search or any structural proof (via Carmichael/Giuga numbers) must start from.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Giuseppe Giuga, Su una presumibile proprieta caratteristica dei numeri primi, Ist. Lombardo Sci. Lett. Rend. A 83 (1950), 511-528 (as cited on the platform parent giuga_conjecture). The lower bound of thousands of digits for a counterexample is due to Borwein, Borwein, Borwein and Girgensohn, Giuga's conjecture on primality, Amer. Math. Monthly 103 (1996) (cited from memory, not re-checked). The range n <= 600 was checked directly in Python for this statement; the statement is the platform theorem giuga_conjecture with the extra hypothesis n <= 600.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem giuga_conjecture_of_le_600 (n : ℕ) (hn : 2 ≤ n) (hle : n ≤ 600) :
    Nat.Prime n ↔
      (∑ k ∈ Finset.Icc 1 (n - 1), (k : ZMod n) ^ (n - 1)) = (-1 : ZMod n) := by sorry
end LefebvreVariations
