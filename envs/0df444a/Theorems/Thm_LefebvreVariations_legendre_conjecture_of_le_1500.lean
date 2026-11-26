-- Prove2me | Theorems.Thm_LefebvreVariations_legendre_conjecture_of_le_1500
-- name    : LefebvreVariations.legendre_conjecture_of_le_1500
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:03:52.42984+00:00
-- url     : https://prove2.me/theorems/07498122-5d6d-441d-8556-98e80f4aad84
-- title:
--   Lefebvre's variations, No. 46 — on a theme by Legendre: Legendre's conjecture holds for n <= 1500
-- statement:
--   For every integer $n$ with $1\le n\le 1500$ there is a prime $p$ with $n^2<p<(n+1)^2$.
--
--   This is Legendre's conjecture (one of Landau's four problems) for $n\le 1500$, that is, for all primes below $1501^2=2\,253\,001$.
--
--   **Formalization Note** The conclusion is copied from the parent `legendre_conjecture`: `∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p`; the only addition is the hypothesis `n ≤ 1500`. For $n=1$ the interval is $(1,4)$ containing $2,3$.
--
--   **Why this is a variation.** This is a variation of the open platform problem legendre_conjecture (Legendre's conjecture on primes between consecutive squares). It is the first explicit finite range, n <= 1500, stated with the parent's own conclusion. It is a partial result that any conditional or computational attack on prime gaps of size about 2*sqrt(p) can use as its verified base.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A.-M. Legendre, Essai sur la theorie des nombres (1798; the conjecture is attributed to him) and E. Landau, Proc. Fifth Internat. Congress of Mathematicians, Cambridge 1912 (Landau's four problems); both cited from memory, not re-checked. The conjecture has been verified by computer far beyond this range; the range n <= 1500 was checked directly in Python for this statement. It is the platform theorem legendre_conjecture with the extra hypothesis n <= 1500.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem legendre_conjecture_of_le_1500 :
    ∀ n : ℕ, 1 ≤ n → n ≤ 1500 → ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p := by sorry
end LefebvreVariations
