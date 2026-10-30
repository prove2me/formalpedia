-- Prove2me | Theorems.Thm_LL_Decomp126b_pocklington_divisors
-- name    : LL_Decomp126b.pocklington_divisors
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:51:55.204083+00:00
-- url     : https://prove2.me/theorems/bb4973cf-9a05-43bc-81dd-00ee38758e38
-- title:
--   Pocklington divisor property
-- statement:
--   Let $N,R,F\in\mathbb N$ with $N\ge2$, $F\ge2$ and $N=RF+1$, and let $a\in\mathbb Z$ satisfy $a^{N-1}\equiv1\pmod N$ and $\gcd(a^{(N-1)/p}-1,N)=1$ for every prime $p\mid F$, where $(N-1)/p$ is natural-number division. Then every divisor $d>1$ of $N$ has the form $d=kF+1$ for some natural number $k\ge1$.
-- source:
--   O. Ramaré and Y. Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), 10 to 33. ; Lemma 8 and its proof, p. 27; first sentence of the proof, citing Brillhart, Lehmer and Selfridge

import Mathlib

namespace LL_Decomp126b
theorem pocklington_divisors {N R F : ℕ} (hN2 : 2 ≤ N) (hF2 : 2 ≤ F)
    (hN : N = R * F + 1) {a : ℤ} (ha : Int.ModEq (N : ℤ) (a ^ (N - 1)) 1)
    (hgcd : ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
    ∀ d : ℕ, d ∣ N → 1 < d → ∃ k : ℕ, 0 < k ∧ d = k * F + 1 := by sorry
end LL_Decomp126b
