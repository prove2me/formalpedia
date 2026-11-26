-- Prove2me | Theorems.Thm_LefebvreVariations_no_odd_extraordinary
-- name    : LefebvreVariations.no_odd_extraordinary
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:26:46.391476+00:00
-- url     : https://prove2.me/theorems/621800b0-77a0-4a7d-87f7-932f43e5513e
-- title:
--   Lefebvre's variations, No. 22 — on a theme by Caveney, Nicolas and Sondow: no odd number is extraordinary
-- statement:
--   This is the statement that no odd integer is extraordinary.
--
--   Let $G(n)=\dfrac{\sigma(n)}{n\log\log n}$, where $\sigma$ is the sum of divisors. Following Caveney, Nicolas and Sondow, a composite number $n>1$ is *extraordinary* if
--
--   1. $G(n/p)\le G(n)$ for every prime $p\mid n$, and
--   2. $G(kn)\le G(n)$ for every integer $k\ge2$.
--
--   Then no odd $n$ is extraordinary. Indeed, for odd composite $n\ge9$ one has $\sigma(2n)=3\sigma(n)$, and
--
--   $$
--   G(2n)>G(n)\iff 3\log\log n>2\log\log(2n)\iff(\log 2n)^2<(\log n)^3,
--   $$
--
--   which holds for every $n\ge9$, so condition 2 fails at $k=2$.
--
--   Caveney, Nicolas and Sondow showed that the Riemann Hypothesis is equivalent to $4$ being the only extraordinary number; this statement disposes of all odd candidates unconditionally.
--
--   **Why this is a variation.** This varies the open problem `BroughanRH.extraordinary`, from the Caveney–Nicolas–Sondow reformulation of the Riemann Hypothesis: RH holds if and only if $4$ is the only extraordinary number. It is an unconditional partial result, showing that no odd number is extraordinary, so the odd candidates are ruled out without assuming RH. Settling it narrows the search for a counterexample, and hence for a failure of RH, to even numbers.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Definition and RH-equivalence: G. Caveney, J.-L. Nicolas and J. Sondow, Robin's theorem, primes, and a new elementary reformulation of the Riemann Hypothesis, Integers 11 (2011), A33 (RH holds iff 4 is the only extraordinary number). The statement here is the elementary k = 2 test σ(2n) = 3σ(n) for odd n. Parent problem: BroughanRH.extraordinary.

import Mathlib

namespace LefebvreVariations

/-- No odd number is extraordinary (Caveney–Nicolas–Sondow): for odd composite `n`, the
multiple `2n` already breaks GA2, since `3 loglog n > 2 loglog 2n` once `n ≥ 9`. -/
theorem no_odd_extraordinary :
    let G (n : ℕ) : ℝ := ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / ((n : ℝ) * Real.log (Real.log n))
    ∀ n : ℕ, Odd n →
      ¬ ((1 < n ∧ ¬ n.Prime) ∧ (∀ p : ℕ, p.Prime → p ∣ n → G (n / p) ≤ G n) ∧
         (∀ k : ℕ, 2 ≤ k → G (k*n) ≤ G n)) := by
  sorry

end LefebvreVariations
