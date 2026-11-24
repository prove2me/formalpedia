-- Prove2me | Theorems.Thm_LefebvreVariations_catalanMersenne_prime_of_le_four
-- name    : LefebvreVariations.catalanMersenne_prime_of_le_four
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T23:19:55.704566+00:00
-- url     : https://prove2.me/theorems/a67e4188-a4e8-4840-a606-6a49bf39180b
-- title:
--   Lefebvre's variations: the first five Catalan–Mersenne numbers are prime
-- statement:
--   This shows that the first five Catalan–Mersenne numbers are prime.
--
--   Let $c_0=2$ and $c_{n+1}=2^{c_n}-1$, the Catalan–Mersenne sequence $2,3,7,127,2^{127}-1,\dots$. Then $c_n$ is prime for $0\le n\le4$.
--
--   The first four values are small primes; $c_4=2^{127}-1$ is the Mersenne prime found by Lucas in 1876 and is certified by the Lucas–Lehmer test.
--
--   Catalan conjectured in 1876 that every term of the sequence is prime. The conjecture is open, and $c_5=2^{2^{127}-1}-1$ is far beyond any possible primality test; the known range is exactly the first five terms.
--
--   **Formalization Note** The sequence is the mission's `FCP.Mersenne.catalanMersenne`.
-- source:
--   E. Catalan, Question 1196, Nouvelles Correspondance Mathématique 2 (1876), 94–96 (the conjecture; page range cited from memory); E. Lucas, Théorie des fonctions numériques simplement périodiques, Amer. J. Math. 1 (1878), 184–240 and 289–321 (primality of 2^127 − 1). Parent problem: FCP.Mersenne.catalan_mersenne_conjecture.

import Definitions.Def_FCP_Mersenne

set_option autoImplicit false

namespace LefebvreVariations

open FCP.Mersenne

/-- **The first five Catalan–Mersenne numbers are prime** (the known range of the Catalan–Mersenne
problem): `c₀ = 2`, `c₁ = 3`, `c₂ = 7`, `c₃ = 127`, `c₄ = 2¹²⁷ − 1` are all prime. Catalan 1876 (a
question in *Nouvelle correspondance mathématique* 2) and Lucas 1876 for `M₁₂₇` (*Bull. Boll. Bibl.
Storia Sci. Mat. Fis.* 10 (1877) 129–193 — page numbers not verified), here via Mathlib's
Lucas–Lehmer test; Wagstaff's heuristic and the primality of `c₅ = 2^(2¹²⁷−1) − 1`
(over `10³⁷` digits) are the open part. -/
theorem catalanMersenne_prime_of_le_four (n : ℕ) (hn : n ≤ 4) : Nat.Prime (catalanMersenne n) := by
  sorry

end LefebvreVariations
