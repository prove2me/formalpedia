-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_classical_step
-- name    : OAI.TwoPointCorrelations.halasz_classical_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:57.085309+00:00
-- url     : https://prove2.me/theorems/2272a8c7-4774-4533-b2c4-847ee591e1df
-- title:
--   One step of the classical Vinogradov mean-value recursion
-- statement:
--   There is $R_0\in\mathbb N$ such that for all naturals $s,k,N,R$ with $s>0$, $k\ge2$, $(4k^2)^2<N$, $k<R$, $N<R^k$, $R\ge R_0$ and $(2k^3+1)^2\le R$,
--
--   $$J_{k+s,k}(N)\le2(2k^3+1)(16R)^{2s}\,k^k(16R)^{k(k-1)/2}\,N^k\,J_{s,k}(\lfloor N/R\rfloor+1),$$
--
--   where $J_{s,k}(N)$ = `halaszVinogradovCount s k N` is the bundle's Vinogradov count: the number of pairs $x,y\in\{1,\dots,N\}^s$ with $\sum_ix_i^j=\sum_iy_i^j$ for $j=1,\dots,k$ (the sum over $x$ of the size of the fibre `halaszVinogradovFiber x k`, with coordinates shifted by one), and $k(k-1)/2$ and $N/R$ are natural-number divisions.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_classical_step`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem halasz_classical_step : ∃ R₀ : ℕ, ∀ s k N R : ℕ,
    0< s → 2≤ k → (4*(k:ℝ)^2)^2<(N:ℝ) → k< R → N< R^k →
    R₀≤ R → (2*(k^2*k)+1)^2≤ R →
    halaszVinogradovCount (k+s) k N ≤
      2*(2*(k^2*k)+1)*((16*R)^(2*s)*((k^k*(16*R)^(k*(k-1)/2))*
        (N^k*halaszVinogradovCount s k (N/R+1)))) := by
  sorry

end OAI.TwoPointCorrelations
