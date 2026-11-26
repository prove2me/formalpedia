-- Prove2me | Theorems.Thm_LefebvreVariations_lehmer_totient_two_prime_factors
-- name    : LefebvreVariations.lehmer_totient_two_prime_factors
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:12:08.236+00:00
-- url     : https://prove2.me/theorems/60dcf3c4-a7c4-4b18-9aca-68f6ef63aee7
-- title:
--   Lefebvre's variations, No. 167 — on a theme by Lehmer: Lehmer's totient problem holds for integers with at most two distinct prime factors
-- statement:
--   Let $n>1$ be an integer with at most two distinct prime factors such that $\varphi(n)\mid n-1$. Then $n$ is prime.
--
--   This is Lehmer's totient problem ($\varphi(n)\mid n-1$ forces $n$ prime) restricted to $\omega(n)\le2$. Lehmer (1932) showed that a composite counterexample would have at least $7$ distinct prime factors, and Cohen–Hagis (1980) at least $14$; the case $\omega(n)\le 2$ is elementary.
--
--   **Formalization Note** `Nat.totient n ∣ n - 1` with natural subtraction (harmless since $n>1$); `(Nat.primeFactors n).card ≤ 2` counts distinct primes. The hypothesis `1 < n` is the parent's.
--
--   **Why this is a variation.** Variation on the open LehmerTotient.lehmer_totient (phi(n) | n-1 implies n prime). It adds the hypothesis omega(n) <= 2, the first finite-complexity slice below the known bound omega >= 7 for a counterexample; the conclusion is the parent's. It extends lehmer_prime_power (omega = 1).
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   D. H. Lehmer, On Euler's totient function, Bull. Amer. Math. Soc. 38 (1932) 745-751 (cited from memory: a composite n with phi(n) | n-1 is odd, squarefree and has at least 7 prime factors); G. L. Cohen and P. Hagis Jr., On the number of prime factors of n if phi(n) | n-1, Nieuw Arch. Wisk. (3) 28 (1980) 177-185 (cited from memory). The omega <= 2 case is an elementary consequence of the definitions; truth checked by computer for all n < 300000 (no composite solution). Origin: platform theorem LehmerTotient.lehmer_totient (Open).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Lehmer's totient problem for integers with at most two distinct prime factors: if `φ(n) ∣ n - 1`
then `n` is prime. The conclusion is the parent's `LehmerTotient.lehmer_totient`. -/
theorem lehmer_totient_two_prime_factors {n : ℕ} (hn : 1 < n)
    (h : Nat.totient n ∣ n - 1) (hω : (Nat.primeFactors n).card ≤ 2) : Nat.Prime n := by
  sorry

end LefebvreVariations
