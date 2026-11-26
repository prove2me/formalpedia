-- Prove2me | Theorems.Thm_LefebvreVariations_mersenne_prime_iff_le_127
-- name    : LefebvreVariations.mersenne_prime_iff_le_127
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T23:16:40.233114+00:00
-- url     : https://prove2.me/theorems/bbe7334d-f3af-4efa-a22d-6b542d468d5f
-- title:
--   Lefebvre's variations, No. 44 — on a theme by Mersenne: the Mersenne primes with exponent up to 127
-- statement:
--   This determines which Mersenne numbers $2^p-1$ are prime for exponents $p\le127$.
--
--   For every $p\le127$,
--
--   $$
--   2^p-1\ \text{is prime}\iff p\in\{2,3,5,7,13,17,19,31,61,89,107,127\}.
--   $$
--
--   The twelve listed exponents are certified by the Lucas–Lehmer test; for every other $p\le127$ an explicit proper factor exists (for a composite $p$ the number $2^q-1$ with $q$ a prime factor of $p$, and for the nineteen primes $11,23,29,\dots,113$ a known prime factor such as $23\mid2^{11}-1$ or $47\mid2^{23}-1$).
--
--   Whether there are infinitely many Mersenne primes is open; this is the first verified range of the problem, going back to Lucas, Pervushin, Powers and Lehmer.
--
--   **Formalization Note** The statement uses Mathlib's `mersenne p` $=2^p-1$; the cases $p=0,1$ (where $2^p-1\in\{0,1\}$ is not prime) are included.
--
--   **Why this is a variation.** This varies the Mersenne prime problem, which asks which $2^p-1$ are prime. It is the first non-trivial range: for $p\le 127$ the exponents giving a prime are exactly $2,3,5,7,13,17,19,31,61,89,107,127$. It settles the parent on its first, fully known stretch and fixes the base cases for any general statement about Mersenne exponents.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   E. Lucas, Théorie des fonctions numériques simplement périodiques, Amer. J. Math. 1 (1878), 184–240 and 289–321 (Lucas–Lehmer test; M_127); D. H. Lehmer, On Lucas's test for the primality of Mersenne's numbers, J. London Math. Soc. 10 (1935), 162–165, and Ann. of Math. 31 (1930), 419–448; M_61: I. M. Pervushin (1883); M_89, M_107: R. E. Powers (1911, 1914). Page numbers of the individual announcements not verified. Parent problem: FCP.Mersenne.infinitely_many_mersenne_primes.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- **The Mersenne primes with exponent at most 127** (first non-trivial range of the
Mersenne-prime problem): for `p ≤ 127`, `2^p − 1` is prime exactly for
`p ∈ {2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127}`. Positive side by the Lucas–Lehmer test
(Lucas 1878, *Amer. J. Math.* 1, 289–321; Lehmer 1930/1935, *Ann. of Math.* 31, 419–448), with
`M₆₁` (Pervushin 1883), `M₈₉` (Powers 1911), `M₁₀₇` (Powers 1914), `M₁₂₇` (Lucas 1876); negative side
by explicit factors of `2^p − 1` for the other primes `p ≤ 113` (and `p` composite or `≤ 1`).
Page numbers of the individual papers not verified here. -/
theorem mersenne_prime_iff_le_127 (p : ℕ) (hp : p ≤ 127) :
    (mersenne p).Prime ↔ p ∈ ({2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127} : Finset ℕ) := by
  sorry

end LefebvreVariations
