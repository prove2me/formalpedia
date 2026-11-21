-- Prove2me | Theorems.Thm_MasulloAudit_euler_partial_products_tendsto_top
-- name    : MasulloAudit.euler_partial_products_tendsto_top
-- status  : Proved
-- author  : @lll
-- created : 2026-11-21T00:51:10.263224+00:00
-- url     : https://prove2.me/theorems/b7fad257-2408-46d0-a2c5-327067d573d6
-- title:
--   Partial Euler products of $\zeta$ diverge for real $0<s\le1$
-- statement:
--   Let $0<s\le1$ be real. Then the partial Euler products of the Riemann zeta function diverge to $+\infty$:
--
--   $$
--   \prod_{p\le x}\bigl(1-p^{-s}\bigr)^{-1}\longrightarrow+\infty\qquad(x\to\infty).
--   $$
--
--   On p. 39 of Masullo's draft, the obstruction to degenerating global θ-functions into S-local ones within normed completions is attributed to the fact that "infinite Euler products do not converge absolutely within the critical strip, by Mertens' Theorem". In fact the partial products diverge to $+\infty$ at every real point $0<s\le1$. There all factors exceed $1$, so absolute and ordinary convergence coincide. This holds unconditionally, because $\sum_p p^{-s}=\infty$; Mertens' theorem concerns only $s=1$. The theorem concerns real $s$ only.
--
--   **Formalization Note.** The product runs over primes $p\le x$, written as `Finset.filter Nat.Prime (Finset.range (x+1))`, with real powers $p^{-s}$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, §1.8, p. 39.

import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Filter

namespace MasulloAudit

/-- Audit of Masullo's draft (p. 39), which attributes the obstruction to degenerating global
θ-functions to S-local ones to the fact that "infinite Euler products do not converge absolutely
within the critical strip, by Mertens' Theorem". In fact, for real `0 < s ≤ 1` the partial Euler
products `∏_{p ≤ x} (1 - p^{-s})⁻¹` of ζ diverge to `+∞` (not merely non-absolutely). -/
theorem euler_partial_products_tendsto_top (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun x : ℕ => ∏ p ∈ Finset.filter Nat.Prime (Finset.range (x + 1)),
      (1 - (p : ℝ) ^ (-s))⁻¹) atTop atTop := by
  sorry

end MasulloAudit
