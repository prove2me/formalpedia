-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_mixed_mean_numeric
-- name    : OAI.TwoPointCorrelations.halasz_mixed_mean_numeric
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:53.287974+00:00
-- url     : https://prove2.me/theorems/9f06235e-e337-4d56-91af-f839686e00ce
-- title:
--   A Ramaré-type identity: log N times the mean of B is controlled by the mixed double convolution
-- statement:
--   Let $G,B:\mathbb N\to\mathbb C$ be bounded by $1$ on positive integers, $N\in\mathbb N$, and $R$ real with $1\le R\le N/2$ and $\log\log N\ge1$. Suppose $B(pm)=G(p)B(m)$ for every prime $p>R$ and every $m\ge1$. Then
--
--   $$\log N\,\Big|\sum_{n=1}^NB(n)\Big|\le\big|\texttt{halaszMixedDouble}\ G\ B\ N\ R\big|+c_0\,N(1+\log R)\log\log N,$$
--
--   where $c_0$ is the explicit constant `halaszMixedNumericConstant` of the bundle (built from `halaszPrimePowerConstant`, `halaszMertensConstant` and `halaszDenominatorConstant`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_mixed_mean_numeric`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset

theorem halasz_mixed_mean_numeric (G B : ℕ → ℂ) (hG : OneBounded G)
    (hB : OneBounded B) (N : ℕ) {R : ℝ} (hR : 1 ≤ R) (hRN : R ≤ (N:ℝ)/2)
    (hll : 1 ≤ Real.log (Real.log (N:ℝ)))
    (hmul : ∀ p : ℕ, p.Prime → R < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    Real.log (N:ℝ)*‖∑ n ∈ Icc 1 N, B n‖ ≤ ‖halaszMixedDouble G B N R‖ +
      halaszMixedNumericConstant*(N:ℝ)*(1+Real.log R)*Real.log (Real.log N) := by
  sorry

end OAI.TwoPointCorrelations
