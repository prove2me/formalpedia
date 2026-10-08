-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_prime_window_exception
-- name    : OAI.TwoPointCorrelations.halasz_prime_window_exception
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:40.737375+00:00
-- url     : https://prove2.me/theorems/ecc02a86-d912-4e27-b2dc-e6e36ee37f07
-- title:
--   The Perron-window integral of two prime polynomials against a function large only near one frequency
-- statement:
--   There are $C>0$ and $B\ge2$ such that for all reals $x>0$, $\delta\in(0,1]$, $T\ge B$, $A,W\ge0$, $c$, all finite sets $P$ of primes $p\ge T^2$ and $Q$ of primes, all $a,b:\mathbb N\to\mathbb C$ and $F:\mathbb R\to\mathbb C$: writing $P_1(t)=\sum_{p\in P}a(p)\frac{\log p}{p}p^{-it}$, $Q_1(t)=\sum_{q\in Q}b(q)\frac{\log q}{q}q^{-it}$ and $K(s)$ = `halaszPerronWindowKernel x δ s` $=\big((1+\delta)\kappa((1+\delta)x,s)-\kappa(x,s)\big)/\delta$ with $\kappa$ the bundle's Perron kernel `modFivePerronKernel`, if $t\mapsto P_1Q_1F\,K(1+it)$ is integrable on $(-T,T]$, $|F(t)|\le A$ on $(-T,T]\setminus(c-\frac12,c+\frac12]$ and $|F|\le W$ on $(-T,T]$, then
--
--   $$\Big|\int_{-T}^{T}P_1(t)Q_1(t)F(t)K(1+it)\,dt\Big|\le Cx\Big(A+\frac W{1+|c|}\Big)\Big(\sum_P|a(p)|^2\tfrac{\log p}p\Big)^{1/2}\Big(\sum_Q|b(q)|^2\tfrac{\log q}q\Big)^{1/2}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_prime_window_exception`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory

theorem halasz_prime_window_exception : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (x δ T A W c : ℝ), 0 < x → 0 < δ → δ ≤ 1 → B ≤ T → 0 ≤ A → 0 ≤ W →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T^2 ≤ (p:ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ (a b : ℕ → ℂ) (F : ℝ → ℂ),
      let P₁ := mrtExponentialPolynomial P
        (fun p => a p*((Real.log (p:ℝ)/p:ℝ):ℂ)) (fun p => -Real.log (p:ℝ))
      let Q₁ := mrtExponentialPolynomial Q
        (fun q => b q*((Real.log (q:ℝ)/q:ℝ):ℂ)) (fun q => -Real.log (q:ℝ))
      IntegrableOn (fun t => P₁ t*Q₁ t*F t*
        halaszPerronWindowKernel x δ (1+(t:ℂ)*Complex.I)) (Set.Ioc (-T) T) →
      (∀ t ∈ Set.Ioc (-T) T, t ∉ Set.Ioc (c-1/2) (c+1/2) → ‖F t‖ ≤ A) →
      (∀ t ∈ Set.Ioc (-T) T, ‖F t‖ ≤ W) →
      ‖∫ t in -T..T, P₁ t*Q₁ t*F t*
        halaszPerronWindowKernel x δ (1+(t:ℂ)*Complex.I)‖ ≤
      (C*x*(A+W/(1+|c|)))*
        (Real.sqrt (∑ p ∈ P, ‖a p‖^2*(Real.log (p:ℝ)/p))*
          Real.sqrt (∑ q ∈ Q, ‖b q‖^2*(Real.log (q:ℝ)/q))) := by
  sorry

end OAI.TwoPointCorrelations
