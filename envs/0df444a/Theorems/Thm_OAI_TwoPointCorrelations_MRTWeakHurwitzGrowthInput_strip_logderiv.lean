-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_strip_logderiv
-- name    : OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.strip_logderiv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:27.128891+00:00
-- url     : https://prove2.me/theorems/8f37469d-ccc5-4943-bca9-12b33e841456
-- title:
--   Under the weak Hurwitz growth input, a Vinogradov–Korobov zero-free strip with a bound for L′/L
-- statement:
--   Assume `MRTWeakHurwitzGrowthInput`. Then there are $c,C,T>0$ such that for every natural $q\ne0$, every Dirichlet character $\chi$ modulo $q$ and reals $t,\sigma$ with $|t|\ge T$ and $1-c\,r(2t)/w_q(2t)\le\sigma\le1+r(2t)/16$,
--
--   $$L(\sigma+it,\chi)\ne0\qquad\text{and}\qquad\Big|\frac{L'(\sigma+it,\chi)}{L(\sigma+it,\chi)}\Big|\le C\,w_q(2t)^2\,\ell(2t)^{2/3},$$
--
--   with $\ell(t)=\log(|t|+3)$, $r(t)=\ell(t)^{-2/3}$ and $w_q(t)=1+\log q+\log\ell(t)$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.strip_logderiv`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Filter
open scoped Classical
open scoped Topology

theorem MRTWeakHurwitzGrowthInput.strip_logderiv (h : MRTWeakHurwitzGrowthInput) :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧ ∀ (q : ℕ) [NeZero q],
      ∀ (χ : DirichletCharacter ℂ q) (t σ : ℝ), T ≤ |t| →
      1 - c * mrtVKRadius (2 * t) / mrtVKWeight q (2 * t) ≤ σ →
      σ ≤ 1 + mrtVKRadius (2 * t) / 16 →
        DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
            C * (mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) := by
  sorry

end OAI.TwoPointCorrelations
