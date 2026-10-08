-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_MRTShortExponentialInput_dilated_forward_windows
-- name    : OAI.TwoPointCorrelations.MRTShortExponentialInput.dilated_forward_windows
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:44.969057+00:00
-- url     : https://prove2.me/theorems/12ad048d-ecdf-41b5-bea0-7a885fb0adc9
-- title:
--   Under the Matomäki–Radziwiłł input, forward windows of a dilated nonpretentious multiplicative function are small
-- statement:
--   Assume `MRTShortExponentialInput`. Let $f$ be uniformly nonpretentious (the comparator `UniformlyNonpretentious`) and bounded by $1$ on positive integers, and $C_0\ge1$. Then there is $C>0$ such that for all sufficiently large $B$: for every finite set $P$ and natural $D$ with $\frac12\exp(B^{9999/10000})\le D\le\exp(C_0B^2)$ and every $q\ge1$, for all sufficiently large $Y$, every multiplicative $b$ bounded by $1$ with $b(p)=f(p)$ for all primes $p\notin P$, and every $\theta\in\mathbb R/\mathbb Z$,
--
--   $$\sum_{v=0}^{Y-1}\Big|\sum_{m=1}^{D}b\big(q(v+1+m)\big)e(m\theta)\Big|\le C\,D\,Y\,\frac{\log B}{B^{9999/10000}}\prod_{p\mid q}\big(1-p^{-1/2}\big)^{-1},$$
--
--   where the inner sum is `forwardWindowPolynomial (n ↦ b(qn)) D (v+1) θ` (a Fourier polynomial with frequencies $m$) and the product is `smoothReciprocalProduct q.primeFactors (1/2)`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.MRTShortExponentialInput.dilated_forward_windows`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem MRTShortExponentialInput.dilated_forward_windows
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ),
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
      ∀ θ : AddCircle (1 : ℝ),
      (∑ v ∈ range Y, ‖forwardWindowPolynomial (fun n => b (q * n)) D (v + 1) θ‖) ≤
        C * D * Y * (Real.log B / B ^ (9999 / 10000 : ℝ)) *
          smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  sorry

end OAI.TwoPointCorrelations
