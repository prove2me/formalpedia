-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_riesz_boundary
-- name    : OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_boundary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:53.719329+00:00
-- url     : https://prove2.me/theorems/6d5e92f2-270a-4dd8-aba7-617b39e52d4d
-- title:
--   Under the weak Hurwitz growth input, ζ has no zeros on a thin rectangle and ζ′/ζ is O(L²) on its boundary
-- statement:
--   Assume `MRTWeakHurwitzGrowthInput`. Then there are $K>0$ and $L_0$ such that for every $L\ge\max(L_0,1)$ with $L^{-3/4}\le\frac12$ and all reals $b\in(1,2]$, $T\in[2,2e^{2L}]$ and $u$ with $|u|\le T/2$, writing $\sigma_0=1-L^{-3/4}$:
--
--   1. $\zeta(s+iu)\ne0$ for every $s$ in the closed rectangle with corners $\sigma_0-iT$ and $b+iT$ (Mathlib-style `Rectangle` of the bundle) with $s+iu\ne1$;
--   2. $|\zeta'/\zeta(\sigma_0+it+iu)|\le KL^2$ for every $t\in[-T,T]$;
--   3. $|\zeta'/\zeta(\sigma+it+iu)|\le KL^2$ for every $\sigma\in[\sigma_0,b]$ and $|t|=T$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_boundary`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Filter
open Set
open scoped Topology

theorem MRTWeakHurwitzGrowthInput.riesz_boundary (h : MRTWeakHurwitzGrowthInput) :
    ∃ K L₀ : ℝ, 0 < K ∧ ∀ L : ℝ, L₀ ≤ L → 1 ≤ L →
      L ^ (-(3 / 4 : ℝ)) ≤ 1 / 2 → ∀ b T u : ℝ,
      1 < b → b ≤ 2 → 2 ≤ T → T ≤ 2 * Real.exp (2 * L) → |u| ≤ T / 2 →
      (∀ s ∈ Rectangle
        (((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) - Complex.I * (T : ℂ))
        ((b : ℂ) + Complex.I * (T : ℂ)),
        s + (u : ℂ) * Complex.I ≠ 1 → riemannZeta (s + (u : ℂ) * Complex.I) ≠ 0) ∧
      (∀ t ∈ Icc (-T) T,
        ‖-deriv riemannZeta
            (((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
          riemannZeta
            (((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤
          K * L ^ 2) ∧
      (∀ σ ∈ Icc (1 - L ^ (-(3 / 4 : ℝ))) b, ∀ t : ℝ, |t| = T →
        ‖-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ K * L ^ 2) := by
  sorry

end OAI.TwoPointCorrelations
