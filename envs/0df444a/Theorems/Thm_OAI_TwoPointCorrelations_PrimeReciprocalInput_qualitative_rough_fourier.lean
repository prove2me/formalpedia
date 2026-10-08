-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_PrimeReciprocalInput_qualitative_rough_fourier
-- name    : OAI.TwoPointCorrelations.PrimeReciprocalInput.qualitative_rough_fourier
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:06.935496+00:00
-- url     : https://prove2.me/theorems/714bba42-de46-444f-8407-6a9f7841b02d
-- title:
--   Under Mertens' estimate, uniform and fourth-moment bounds for weighted Fourier sums over rough numbers
-- statement:
--   Assume `PrimeReciprocalInput` (there is $C$ with $|\sum_{p\le y}1/p-\log\log y|\le C$ for all $y\ge2$). Then there are $U,V>0$ such that for all sufficiently large $B$: for all naturals $D\ge\frac12\exp(B^{9999/10000})$ and $h>0$, every finite set $Z$ of integers $z\in[D,2D)$ having no prime factor below $\exp(B^{9999/10000})$ (`HasNoPrimeFactorBelow`), and every $c:\mathbb N\to\mathbb C$ with $|c|\le1$ on $Z$, the polynomial $\Phi(\theta)=\sum_{z\in Z}\frac{c(z)}z\,e(hz\theta)$ on $\mathbb R/\mathbb Z$ (`weightedRoughFourier Z c h`) satisfies
--
--   $$\sup_\theta|\Phi(\theta)|\le U\frac{\log B}{B^{9999/10000}}\qquad\text{and}\qquad\int_{\mathbb R/\mathbb Z}|\Phi|^4\,d\theta\le\frac VD\Big(\frac{\log B}{B^{9999/10000}}\Big)^4,$$
--
--   the integral against Haar probability measure on the circle.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.PrimeReciprocalInput.qualitative_rough_fourier`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open MeasureTheory
open scoped Classical

theorem PrimeReciprocalInput.qualitative_rough_fourier (hM : PrimeReciprocalInput) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (D h : ℕ), (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D → 0 < h →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      (∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤
        U * (Real.log B / B ^ (9999 / 10000 : ℝ))) ∧
      (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤
        V / (D : ℝ) * (Real.log B / B ^ (9999 / 10000 : ℝ)) ^ 4 := by
  sorry

end OAI.TwoPointCorrelations
