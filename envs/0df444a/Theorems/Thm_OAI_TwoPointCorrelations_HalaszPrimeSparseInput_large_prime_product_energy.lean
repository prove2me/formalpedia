-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_HalaszPrimeSparseInput_large_prime_product_energy
-- name    : OAI.TwoPointCorrelations.HalaszPrimeSparseInput.large_prime_product_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:52.391926+00:00
-- url     : https://prove2.me/theorems/a572b660-0b14-4fe4-8d2b-2c51df423412
-- title:
--   Under the sparse prime large-values input, the product energy of a short prime polynomial with a cofactor polynomial
-- statement:
--   Assume `HalaszPrimeSparseInput`: there are $C,L_0$ with $C>0$ such that for all $L\ge\max(L_0,1)$, $Y\ge2$, every finite set $P$ of primes in $[Y,2Y]$, every $a:\mathbb N\to\mathbb C$ and every finite set $S$ of reals with $|t|\le e^L$ and pairwise separations at least $1$, $\sum_{t\in S}|\sum_{p\in P}a(p)p^{-it}|^2\le C\big(Y+|S|\,Y e^{-\log Y/L^{3/4}}L^2\big)\sum_{p\in P}|a(p)|^2/\log p$.
--
--   Then there are $C>0$ and $B_0\ge2$ such that for all sufficiently large $L$: for reals $H\ge B_0$, $Y\ge2$ with $H^2\le Y$, $L^{79/80}\le\log Y\le L$ and $\log Y\ge1$; every finite set $P$ of primes in $[Y,2Y]$ with $\log Y\le\log p\le\log Y+1/H$; every $F:\mathbb N\to\mathbb C$ bounded by $1$ on positive integers; every finite set $A$, $B:\mathbb N\to\mathbb C$, natural $N$, reals $a$ and $U\ge0$; and every measurable $E\subseteq(-e^L,e^L]$: writing $\mathcal P(t)=\sum_{p\in P}\frac{F(p)}{p}p^{-it}$ (`mrtExponentialPolynomial`) and $\mathcal C(t)$ = `mrtCofactorPolynomial A B N a t`, if $|\mathcal C(t)|\le U$ for every $t\in E$ with $|\mathcal P(t)|\ge L^{-100}$, then
--
--   $$\int_{E\cap\{|\mathcal P|\ge L^{-100}\}}|\mathcal P(t)\,\mathcal C(t)|^2\,dt\le\frac{C\,U^2}{H(\log Y)^2}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.HalaszPrimeSparseInput.large_prime_product_energy`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset
open MeasureTheory
open scoped Classical

theorem HalaszPrimeSparseInput.large_prime_product_energy
    (hprime : HalaszPrimeSparseInput) :
    ∃ C B₀ : ℝ, 0 < C ∧ 2 ≤ B₀ ∧ ∀ᶠ L : ℝ in atTop,
      ∀ H Y : ℝ, B₀ ≤ H → 2 ≤ Y → H^2 ≤ Y →
      L^(79/80:ℝ) ≤ Real.log Y → Real.log Y ≤ L → 1 ≤ Real.log Y →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
      (∀ p ∈ P, Real.log Y ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ Real.log Y+1/H) →
      OneBounded F →
      ∀ (A : Finset ℕ) (B : ℕ → ℂ) (N : ℕ) (a U : ℝ), 0 ≤ U →
      ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) →
      (∀ t ∈ E, L^(-100:ℝ) ≤ ‖mrtExponentialPolynomial P
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖ →
        ‖mrtCofactorPolynomial A B N a t‖ ≤ U) →
      (∫ t in E ∩ {t | L^(-100:ℝ) ≤ ‖mrtExponentialPolynomial P
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖},
        ‖mrtExponentialPolynomial P (fun p => F p/(p:ℂ))
          (fun p => -Real.log (p:ℝ)) t * mrtCofactorPolynomial A B N a t‖^2) ≤
        C*U^2/(H*(Real.log Y)^2) := by
  sorry

end OAI.TwoPointCorrelations
