-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_log_dirichlet_block
-- name    : OAI.TwoPointCorrelations.halasz_log_dirichlet_block
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:18.545743+00:00
-- url     : https://prove2.me/theorems/9aae8cd2-3539-433c-a90b-9fc7dd9804cb
-- title:
--   A Vinogradov–Korobov-type bound for short blocks of Hurwitz-type Dirichlet polynomials
-- statement:
--   There is $C\ge1$ such that for all naturals $N\ge1$ and $H\le N$, every $a\in[0,1]$, every $s\in\mathbb C$ with $\operatorname{Re}s\ge2/3$, and reals $L,\lambda$ with $L>0$, $\log N\ge1$, $L=\lambda\log N$, $\lambda\ge49/100$, $N^{2/3}\le N/2$ and $|\operatorname{Im}s|=N^\lambda$,
--
--   $$\Big|\sum_{n=0}^{H-1}(N+a+n)^{-s}\Big|\le C(L+1)^6\exp\!\Big(10^9\max(1-\operatorname{Re}s,0)^{3/2}L\Big)+4.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_log_dirichlet_block`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Complex

theorem halasz_log_dirichlet_block : ∃ C : ℝ, 1≤ C ∧ ∀ N H : ℕ,
    1≤ N → H≤ N → ∀ a : ℝ, a∈Set.Icc (0:ℝ) 1 → ∀ s : ℂ,
    2/3≤ s.re → ∀ L lam : ℝ, 0< L → 1≤ Real.log N →
    L=lam*Real.log N → 49/100≤ lam →
    (N:ℝ)^(2/3:ℝ)≤(N:ℝ)/2 → |s.im|=(N:ℝ)^lam →
    ‖∑ n∈range H,(((N:ℝ)+a+n:ℝ):ℂ)^(-s)‖≤
      C*(L+1)^6*Real.exp ((10^9:ℝ)*(max (1-s.re) 0)^(3/2:ℝ)*L)+4 := by
  sorry

end OAI.TwoPointCorrelations
