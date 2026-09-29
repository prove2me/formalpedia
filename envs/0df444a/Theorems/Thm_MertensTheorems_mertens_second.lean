-- Prove2me | Theorems.Thm_MertensTheorems_mertens_second
-- name    : MertensTheorems.mertens_second
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T05:22:28.73036+00:00
-- url     : https://prove2.me/theorems/1e9b6ab8-670b-4ffa-88f9-7a1dd65658fe
-- title:
--   Mertens' second theorem with explicit error term
-- statement:
--   **Mertens' second theorem** gives the asymptotic for the sum of reciprocals of the primes, with an
--   explicit error term.
--
--   $$\Big|\sum_{p \le n} \frac1p \;-\; \bigl(\log\log n + M\bigr)\Big| \;\le\; \frac{C}{\log n}$$
--
--   The sum runs over primes $p \le n$, and $M$ is the Meissel–Mertens constant, approximately
--   $0.2614972\ldots$. The statement asserts the existence of such an $M$ together with an absolute
--   constant $C$ for which the bound holds for every $n \ge 2$.
--
--   That $\sum_{p \le n} 1/p$ diverges is Euler's theorem, and already shows the primes are infinite and
--   not too sparse. Mertens' refinement pins the rate: the divergence is exactly $\log\log n$, and the
--   approach to it is $O(1/\log n)$. This is one of the foundational estimates of analytic number
--   theory. It is what makes sieve methods quantitative — the Brun and Selberg sieves both need it — and
--   it is the input to the Hardy–Ramanujan and Turán–Kubilius theorems on the normal order of the number
--   of prime factors. Notably, the result predates the prime number theorem and does not depend on it.
--
--   **Formalization note.** The primes up to $n$ are enumerated as
--   `(Finset.range (n+1)).filter Nat.Prime`, so the sum is over a finite set of naturals cast to `ℝ`.
--   Both $M$ and $C$ are existentially quantified, with $C$ required only to be nonnegative. Only
--   Mathlib is needed.
-- source:
--   Mertens' second theorem. Lean proof from the Salt project by Jason Hickey, Salt/Mertens/Second.lean (https://github.com/jyh/salt, Apache-2.0).

import Mathlib

namespace MertensTheorems

/-- Mertens' second theorem, in sharp form: the sum of reciprocals of the primes up to `n`
equals `log log n + M` up to an error `O(1 / log n)`. -/
theorem mertens_second :
    ∃ M : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      |(∑ p ∈ (Finset.range (n+1)).filter Nat.Prime, (1:ℝ)/p)
        - (Real.log (Real.log n) + M)| ≤ C / Real.log n := by
  sorry

end MertensTheorems
