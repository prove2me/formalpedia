-- Prove2me | Theorems.Thm_LefebvreVariations_erdos_406_of_le_pow_100000
-- name    : LefebvreVariations.erdos_406_of_le_pow_100000
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:46:53.619106+00:00
-- url     : https://prove2.me/theorems/631b4fc7-fae2-5b3c-a460-1e601e9beff5
-- title:
--   Lefebvre's variations, No. 55 — on a theme by Erdős: the only powers of two up to 2^100000 with no digit 2 in base 3 are 1, 4 and 256
-- statement:
--   Every power of two $n\le 2^{100000}$ whose base-3 expansion uses only the digits $0$ and $1$ is one of $1$, $4$ or $256$:
--
--   $$
--   \{\,n\in\mathbb{N} : n=2^k \text{ for some } k,\ n\le 2^{100000},\ \text{every base-3 digit of } n \text{ is } 0 \text{ or } 1\,\}=\{1,\,4,\,256\}.
--   $$
--
--   Here $1=1_3$, $4=11_3$ and $256=100111_3$. Erdős conjectured that these three are the only powers of two with no digit $2$ in base $3$ (Erdős problem 406); the parent problem asks for the finiteness of this set. The statement settles the conjecture up to the exponent $100000$.
--
--   **Formalization Note.** The set is written with the parent's own predicates, `n.isPowerOfTwo` and `Nat.digits 3 n ⊆ [0, 1]`, with the added bound `n ≤ 2 ^ 100000`. The digit list `Nat.digits 3 n` is little-endian, and `Nat.digits 3 1 = [1]`, so `n = 1` is included (the exponent $k=0$). The right-hand side is the three-element set `{1, 4, 256}`.
--
--   **Why this is a variation.** Variation on the open Erdos406.erdos_406 (the only powers of two with no digit 2 in base 3 are 1, 4 and 256). It is a finite partial result: the conjecture verified for all powers of two up to 2^100000, which extends the known examples and rules out small counterexamples.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Erdős problem 406 (erdosproblems.com/406): the conjecture that 1, 4 and 256 are the only powers of 2 whose base-3 expansion has only digits 0 and 1. See also J. C. Lagarias, "Ternary expansions of powers of 2", J. London Math. Soc. (2) 79 (2009) (cited from memory). Origin of this statement: it is the range n <= 2^100000 of the open platform problem Erdos406.erdos_406 (finiteness of this set), established here by a finite computation; no similar finite-range statement existed on the platform.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- **Erdős problem 406 up to `2 ^ 100000`**: the powers of two `≤ 2 ^ 100000` whose base-3 digits
are all `0` or `1` are exactly `1`, `4 = 11₃` and `256 = 100111₃`, by finite computation. That
there are no others is Erdős' conjecture (problem 406 on erdosproblems.com); see also Lagarias,
*Ternary expansions of powers of 2*, J. London Math. Soc. (2) 79 (2009) (cited from memory). -/
theorem erdos_406_of_le_pow_100000 :
    { n : ℕ | n.isPowerOfTwo ∧ n ≤ 2 ^ 100000 ∧ Nat.digits 3 n ⊆ [0, 1] } = {1, 4, 256} := by
  sorry

end LefebvreVariations
