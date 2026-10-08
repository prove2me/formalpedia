-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_PrimeReciprocalInput_rough_fourier
-- name    : OAI.TwoPointCorrelations.PrimeReciprocalInput.rough_fourier
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:14.779367+00:00
-- url     : https://prove2.me/theorems/e3dac736-bd27-42e2-afb7-c7a62a7c28ea
-- title:
--   Under Mertens' estimate, uniform and fourth-moment bounds for Fourier sums of 1/z over rough z
-- statement:
--   Assume `PrimeReciprocalInput`. Then there are $U,V>0$ such that for all sufficiently large $L$: for all naturals $D\ge\frac12\exp(L^{199/200})$ and $h>0$, and every finite set $Z$ of integers $z\in[D,2D)$ divisible by no prime $p\le\exp(L^{99/100})$ (`avoidsPrimeSet (sievePrimesUpTo …)`), the polynomial $\Phi(\theta)=\sum_{z\in Z}z^{-1}e(hz\theta)$ (`roughFourierPolynomial Z h`) satisfies
--
--   $$\sup_\theta|\Phi(\theta)|\le U\,L^{-99/100}\qquad\text{and}\qquad\int_{\mathbb R/\mathbb Z}|\Phi|^4\,d\theta\le\frac VD\,L^{-99/25}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.PrimeReciprocalInput.rough_fourier`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open MeasureTheory
open scoped Classical

theorem PrimeReciprocalInput.rough_fourier (hM : PrimeReciprocalInput) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (D h : ℕ), (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ D → 0 < h →
      ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      (∀ θ, ‖roughFourierPolynomial Z h θ‖ ≤ U * L ^ (-99 / 100 : ℝ)) ∧
      (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤
        V / (D : ℝ) * L ^ (-99 / 25 : ℝ) := by
  sorry

end OAI.TwoPointCorrelations
