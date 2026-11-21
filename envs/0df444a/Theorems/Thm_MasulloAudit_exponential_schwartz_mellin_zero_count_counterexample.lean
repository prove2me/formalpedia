-- Prove2me | Theorems.Thm_MasulloAudit_exponential_schwartz_mellin_zero_count_counterexample
-- name    : MasulloAudit.exponential_schwartz_mellin_zero_count_counterexample
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:50:30.721371+00:00
-- url     : https://prove2.me/theorems/2b8f8981-af77-4119-acfa-11e373438d62
-- title:
--   An exponentially Schwartz Mellin transform with exactly 2n+2 distinct zeros in a unit-height box
-- statement:
--   On the positive norm line there is an exponentially Schwartz test $\phi$ whose Mellin transform everywhere is $e^{s^2}(e^{2\pi i s^2}-1)$. For every integer $n\ge1$ there are exactly $2n+2$ distinct zeros in $[-1,1]+i[n,n+1]$. Thus the number of distinct zeros in the boxes at real heights $T\to+\infty$ fails to be $O(\log |T|)$.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Lemma 9.3.2.4, p. 425. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=425. Counterexample for G equal to the positive reals with its usual norm and the trivial character. The additional divisor-containment hypothesis in the next lemma is separate.

import Mathlib
open Set Filter MeasureTheory
open scoped SchwartzMap Asymptotics Topology

theorem MasulloAudit.exponential_schwartz_mellin_zero_count_counterexample :
    ∃ φ : ℝ → ℂ,
      (∀ a : ℝ, ∃ g : 𝓢(ℝ,ℂ), ∀ x : ℝ,
        g x = Complex.exp ((a:ℂ)*x) * φ (Real.exp x)) ∧
      (∀ z : ℂ, HasMellin φ z
        (Complex.exp (z^2) * (Complex.exp (2*(Real.pi:ℂ)*Complex.I*z^2)-1))) ∧
      mellin φ ≠ 0 ∧
      (∀ n : ℕ, 1 ≤ n → ∃ S : Finset ℂ, S.card = 2*n+2 ∧ ∀ z : ℂ,
        z ∈ S ↔ mellin φ z = 0 ∧ z.re ∈ Icc (-1:ℝ) 1 ∧ z.im ∈ Icc (n:ℝ) ((n:ℝ)+1)) ∧
      ¬ (fun T : ℝ => (({z : ℂ | mellin φ z = 0 ∧ z.re ∈ Icc (-1:ℝ) 1 ∧
          z.im ∈ Icc T (T+1)} : Set ℂ).ncard : ℝ)) =O[atTop] (fun T : ℝ => Real.log |T|) := by sorry
