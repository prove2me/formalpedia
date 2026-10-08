-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_qualitative_dilated_fixed_factors
-- name    : OAI.TwoPointCorrelations.qualitative_dilated_fixed_factors
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:46.536978+00:00
-- url     : https://prove2.me/theorems/e3b428d8-effe-4e1b-9a5e-6f9cf0856688
-- title:
--   Under Mertens' estimate and the Matomäki–Radziwiłł input, rough shift averages of dilated nonpretentious functions are small
-- statement:
--   Assume `PrimeReciprocalInput` and `MRTShortExponentialInput`. Let $F,G$ be multiplicative, bounded by $1$ on positive integers, at least one `UniformlyNonpretentious`; $h>0$ and $C_0\ge1$. Then there is $C>0$ such that for all sufficiently large $B$: for every natural $u>0$ and reals $M,\tau$ with $1<\tau<2$ and $\exp(B^{9999/10000})/\tau\le M\le\exp(C_0B^2)$, for all sufficiently large $Y$, and every finite set $Z$ of integers $z\in(M,\tau M]$ with no prime factor below $\exp(B^{9999/10000})$,
--
--   $$\big|\texttt{weightedRoughShiftAverage}\ (n\mapsto F(un))\ (n\mapsto G(un))\ Z\ 1\ h\ Y\big|\le C\,B^{-11/10}\prod_{p\mid u}\big(1-p^{-1/2}\big)^{-1},$$
--
--   where the average is $\frac1Y\sum_{v=1}^{Y}$ of the bundle's profile `weightedRoughShiftProfile` at $v$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.qualitative_dilated_fixed_factors`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem qualitative_dilated_fixed_factors (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {F G : ℕ → ℂ}
    (hFm : Multiplicative F) (hGm : Multiplicative G)
    (hF : OneBounded F) (hG : OneBounded G)
    (hnp : UniformlyNonpretentious F ∨ UniformlyNonpretentious G)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (u : ℕ), 0 < u → ∀ M τ : ℝ, 1 < τ → τ < 2 →
      Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M →
      M ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ᶠ Y : ℕ in atTop, ∀ Z : Finset ℕ,
      (∀ z ∈ Z, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      ‖weightedRoughShiftAverage (fun n => F (u * n)) (fun n => G (u * n))
        Z (fun _ => 1) h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) * smoothReciprocalProduct u.primeFactors (1 / 2 : ℝ) := by
  sorry

end OAI.TwoPointCorrelations
