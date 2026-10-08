-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_logderiv
-- name    : OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.logderiv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:43.154388+00:00
-- url     : https://prove2.me/theorems/e374399c-8062-4e59-8a23-10c8e9ac04b1
-- title:
--   Under the weak Hurwitz growth input, a bound for L′/L just to the right of the line Re s = 1
-- statement:
--   Assume `MRTWeakHurwitzGrowthInput`. Then there are $C,T>0$ such that for every natural $q\ne0$, every Dirichlet character $\chi$ modulo $q$, and reals $t,\sigma$ with $|t|\ge T$ and $1<\sigma\le1+r(2t)/16$,
--
--   $$\Big|\frac{L'(\sigma+it,\chi)}{L(\sigma+it,\chi)}\Big|\le C\,w_q(2t)^2\,\ell(2t)^{2/3},$$
--
--   where $\ell(t)=\log(|t|+3)$ (`mrtVKLog`), $r(t)=\ell(t)^{-2/3}$ (`mrtVKRadius`) and $w_q(t)=1+\log q+\log\ell(t)$ (`mrtVKWeight`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.logderiv`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Filter
open scoped Classical
open scoped Topology

theorem MRTWeakHurwitzGrowthInput.logderiv (h : MRTWeakHurwitzGrowthInput) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ (q : ℕ) [NeZero q],
      ∀ (χ : DirichletCharacter ℂ q) (t σ : ℝ), T ≤ |t| →
      1 < σ → σ ≤ 1 + mrtVKRadius (2 * t) / 16 →
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
            C * (mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) := by
  sorry

end OAI.TwoPointCorrelations
