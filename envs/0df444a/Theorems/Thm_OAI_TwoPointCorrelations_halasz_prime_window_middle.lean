-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_prime_window_middle
-- name    : OAI.TwoPointCorrelations.halasz_prime_window_middle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:55.028744+00:00
-- url     : https://prove2.me/theorems/65e11e26-2883-4113-8ea6-085a4bd2beab
-- title:
--   The Perron-window integral of two prime polynomials against a bounded function
-- statement:
--   There are $C>0$ and $B\ge2$ such that for all reals $x>0$, $\delta\in(0,1]$, $T\ge B$, $A\ge0$, every finite set $P$ of primes $p\ge T^2$, every finite set $Q$ of primes, all $a,b:\mathbb N\to\mathbb C$ and every $F:\mathbb R\to\mathbb C$ with $|F(t)|\le A$ on $[-T,T]$,
--
--   $$\Big|\int_{-T}^{T}P_1(t)\,Q_1(t)\,F(t)\,K(1+it)\,dt\Big|\le CxA\Big(\sum_{p\in P}|a(p)|^2\tfrac{\log p}p\Big)^{1/2}\Big(\sum_{q\in Q}|b(q)|^2\tfrac{\log q}q\Big)^{1/2},$$
--
--   where $P_1(t)=\sum_{p\in P}a(p)\frac{\log p}{p}e^{-it\log p}$, $Q_1(t)=\sum_{q\in Q}b(q)\frac{\log q}{q}e^{-it\log q}$, and $K$ = `halaszPerronWindowKernel x δ` $=\big((1+\delta)\kappa((1+\delta)x,\cdot)-\kappa(x,\cdot)\big)/\delta$ with the bundle's Perron kernel $\kappa$ = `modFivePerronKernel` (the integral is the interval integral, $0$ for a non-integrable integrand).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_prime_window_middle`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open MeasureTheory
open Finset

theorem halasz_prime_window_middle : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (x δ T A : ℝ), 0 < x → 0 < δ → δ ≤ 1 → B ≤ T → 0 ≤ A →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ (a b : ℕ → ℂ) (F : ℝ → ℂ),
      (∀ t ∈ Set.Icc (-T) T, ‖F t‖ ≤ A) →
      ‖∫ t in -T..T,
        mrtExponentialPolynomial P (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
          (fun p => -Real.log (p : ℝ)) t *
        mrtExponentialPolynomial Q (fun q => b q * ((Real.log (q : ℝ) / q : ℝ) : ℂ))
          (fun q => -Real.log (q : ℝ)) t * F t *
        halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)‖ ≤
        (C * x * A) * (Real.sqrt (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) := by
  sorry

end OAI.TwoPointCorrelations
