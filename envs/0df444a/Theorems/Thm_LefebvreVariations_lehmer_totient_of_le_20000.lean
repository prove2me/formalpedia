-- Prove2me | Theorems.Thm_LefebvreVariations_lehmer_totient_of_le_20000
-- name    : LefebvreVariations.lehmer_totient_of_le_20000
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:03:36.999651+00:00
-- url     : https://prove2.me/theorems/d83b4c1d-f4e0-4897-a1e8-655b0137ba7e
-- title:
--   Lefebvre's variations, No. 73 — on a theme by Lehmer: Lehmer's totient conjecture holds for n <= 20000
-- statement:
--   Let $n$ be an integer with $2\le n\le 20000$. If $\varphi(n)\mid n-1$, then $n$ is prime.
--
--   This is Lehmer's totient conjecture restricted to $n\le 20000$. The converse is trivial, since $\varphi(p)=p-1$ for a prime $p$. Composite numbers with $\varphi(n)\mid n-1$ would be Carmichael numbers of a very special kind; none is known.
--
--   **Formalization Note** `Nat.totient n ∣ n - 1` is the parent's hypothesis verbatim, with the additional hypothesis `n ≤ 20000`. Natural subtraction is harmless as $n\ge 2$.
--
--   **Why this is a variation.** This is a variation of the open platform problem lehmer_totient_conjecture (Lehmer's totient conjecture). It is the conjecture at its first non-trivial finite size, n <= 20000, in the parent's own formulation with Nat.totient. Proving it fixes the finite base case that structural attacks (counterexamples must be squarefree Carmichael numbers with many prime factors) take for granted, and gives a template a prover can scale to larger bounds.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   D. H. Lehmer, On Euler's totient function, Bull. Amer. Math. Soc. 38 (1932), 745-751 (as cited on the platform parent lehmer_totient_conjecture). Known lower bounds for a counterexample (at least 14 distinct prime factors, due to Cohen and Hagis, 1980; and a size bound reported on the platform) are cited from memory, not re-checked. The range n <= 20000 was checked directly in Python; the statement is the platform theorem lehmer_totient_conjecture with the extra hypothesis n <= 20000.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem lehmer_totient_of_le_20000 (n : ℕ) (hn : 2 ≤ n) (hle : n ≤ 20000)
    (hdvd : Nat.totient n ∣ n - 1) :
    Nat.Prime n := by sorry
end LefebvreVariations
