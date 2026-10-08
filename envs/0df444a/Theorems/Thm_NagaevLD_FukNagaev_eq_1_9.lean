-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_eq_1_9
-- name    : NagaevLD.FukNagaev.eq_1_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:14.777525+00:00
-- url     : https://prove2.me/theorems/a1ed2212-3c19-49b0-955e-057ede4d21ac
-- title:
--   (1.9), p. 749 — P(S̃_n ≥ x) ≤ e^{−hx}Ee^{hS̃_n} = e^{−hx}Π Ee^{hX̃_i} for h > 0
-- statement:
--   Let $X_1,\dots,X_n$ be independent random variables, $x>0$, $y_1,\dots,y_n>0$, and let $\tilde X_i$ (equal to $X_i$ if $X_i\le y_i$, to $0$ otherwise) and $\tilde S_n=\sum_i\tilde X_i$ be the truncated summands and their sum. Then for every $h>0$,
--   $$P(\tilde S_n\ge x)\le e^{-hx}\,\mathbb E e^{h\tilde S_n}=e^{-hx}\prod_{i=1}^n\mathbb E e^{h\tilde X_i}.$$
--
--   The first inequality is the exponential Chebyshev (Chernoff) bound; the equality uses the independence of the truncated summands. All exponential moments are finite because $\tilde X_i\le y_i$.
--
--   **Formalization Note** The two parts are stated as a conjunction. No integrability hypothesis is needed: $e^{h\tilde X_i}\le e^{hy_i}$.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 749, proof of Theorem 1.3, (1.9)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (h : ℝ) (hh : 0 < h) :
    P.real {ω | x ≤ St X yv ω} ≤ Real.exp (-h * x) * ∫ ω, Real.exp (h * St X yv ω) ∂P ∧
      Real.exp (-h * x) * ∫ ω, Real.exp (h * St X yv ω) ∂P =
        Real.exp (-h * x) * ∏ i, ∫ ω, Real.exp (h * Xt X yv i ω) ∂P := by sorry

end NagaevLD.FukNagaev
