-- Prove2me | Theorems.Thm_LefebvreVariations_fermat_prime_conjecture_of_le_eleven
-- name    : LefebvreVariations.fermat_prime_conjecture_of_le_eleven
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:04:43.037406+00:00
-- url     : https://prove2.me/theorems/9cf33903-3309-4cce-b80a-d5bedff7d617
-- title:
--   Lefebvre's variations, No. 68 — on a theme by Fermat: the Fermat numbers F_n with n at most 11 are prime exactly for n at most 4
-- statement:
--   Among the Fermat numbers $F_n=2^{2^n}+1$ with $0\le n\le 11$, exactly $F_0,F_1,F_2,F_3,F_4$ are prime:
--   $$\{\,n\in\mathbb{N} : n\le 11 \wedge F_n \text{ is prime}\,\}=\{0,1,2,3,4\}.$$
--
--   The Fermat prime conjecture asks whether this set is finite for the whole range of $n$; $F_5,\dots,F_{11}$ are known to be composite by exhibiting explicit factors (for $F_5$ Euler found $641$ in 1732).
--
--   **Formalization Note** The set is the parent's `{n : ℕ | Nat.Prime (2 ^ (2 ^ n) + 1)}` intersected with `n ≤ 11`, and the claim is its exact value. The largest number involved is $F_{11}=2^{2048}+1$.
--
--   **Why this is a variation.** This is a variation of the open platform problem fermat_prime_conjecture (finiteness of the set of Fermat primes). It is the problem played at its first non-trivial finite size: the exact set of n <= 11 with F_n prime, in the parent's own expression. It is a partial result that pins down the initial segment of the set whose finiteness the parent asks about, and provides explicit factorizations a prover can extend.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   P. de Fermat conjectured that all F_n are prime; L. Euler, 1732, F_5 = 641 * 6700417; F_6 factored by F. Landry, 1880 (cited from memory). Factors of F_7 to F_11 are classical (Morrison-Brillhart 1975 for F_7, Brent-Pollard 1981 for F_8, Western 1903 and Cunningham for F_9, Brent 1995 for F_10, Brent 1988 for F_11; all names and dates cited from memory, not re-checked). The statement follows the platform theorem fermat_prime_conjecture, replacing finiteness by the exact value of the set for n <= 11.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem fermat_prime_conjecture_of_le_eleven :
    {n : ℕ | n ≤ 11 ∧ Nat.Prime (2 ^ (2 ^ n) + 1)} = {0, 1, 2, 3, 4} := by sorry
end LefebvreVariations
