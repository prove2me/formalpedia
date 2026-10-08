-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_small_cofactor_integral
-- name    : OAI.TwoPointCorrelations.mrt_small_cofactor_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:24.494118+00:00
-- url     : https://prove2.me/theorems/1d50693d-15e0-49f4-a50c-e4c8fb923a44
-- title:
--   The integral of |Q·cofactor polynomial|² over a sparse set where Q is small
-- statement:
--   Let $A$ be a finite set, $B:\mathbb N\to\mathbb C$ bounded by $1$ on positive integers, $N$ natural, and reals $a\ge1$ with $N/a\ge2$, $T\ge0$, $\theta$. Let $Q:\mathbb R\to\mathbb C$ be continuous and $E\subseteq(-T,T]$ measurable such that $|Q(t)|\le\theta$ on $E$ and every finite $1$-separated subset $S\subseteq E$ satisfies $\#S\cdot E_{\mathrm{sp}}(N/a,T)\le N/a$, where $E_{\mathrm{sp}}$ = `halaszSparseKernelError` $=\frac{440}\pi\sqrt{2T}+\frac{512}{(N/a)(2\pi)^2}\sum_{k\in\mathbb Z}k^{-2}$. Then
--
--   $$\int_E\big|Q(t)\,\mathcal C(t)\big|^2dt\le1190408\,\theta^2,$$
--
--   with $\mathcal C$ = `mrtCofactorPolynomial A B N a`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_small_cofactor_integral`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open scoped Classical

theorem mrt_small_cofactor_integral (A : Finset ℕ) (B : ℕ → ℂ)
    (hB : OneBounded B) (N : ℕ) {a T θ : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) (hT : 0 ≤ T) (Q : ℝ → ℂ) (hQ : Continuous Q)
    {E : Set ℝ} (hE : MeasurableSet E) (hET : E ⊆ Set.Ioc (-T) T)
    (hcost : ∀ S : Finset ℝ, (∀ t ∈ S, t ∈ E) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (S.card:ℝ)*halaszSparseKernelError ((N:ℝ)/a) T ≤ (N:ℝ)/a)
    (hsmall : ∀ t ∈ E, ‖Q t‖ ≤ θ) :
    (∫ t in E, ‖Q t*mrtCofactorPolynomial A B N a t‖^2) ≤ 1190408*θ^2 := by
  sorry

end OAI.TwoPointCorrelations
