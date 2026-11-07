-- Prove2me | Theorems.Thm_MaxEntOCRS_lemma_7
-- name    : MaxEntOCRS.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:30:26.754209+00:00
-- url     : https://prove2.me/theorems/2586bdf0-dcd2-402a-8446-b32ece281e4b
-- title:
--   Lemma 7 — $-\partial_s\partial_t \log f \le \frac14(\partial_s+\partial_t)\log f$ at $(1,1)$
-- statement:
--   Let $f(s, t)$ be a real polynomial in two variables with nonnegative coefficients, $f(1, 1) > 0$, and no zeros with $\operatorname{Re} s > 0$, $\operatorname{Re} t > 0$. Then at $(1, 1)$,
--   $$
--   -\partial_s \partial_t \log f \le \frac14 (\partial_s + \partial_t) \log f ,
--   $$
--   that is, with $f, f_s, f_t, f_{st}$ evaluated at $(1,1)$,
--   $$
--   -\Big(\frac{f_{st}}{f} - \frac{f_s f_t}{f^2}\Big) \le \frac14\Big(\frac{f_s}{f} + \frac{f_t}{f}\Big).
--   $$
--   The bound is attained by $f = s + t$. It is the bivariate inequality behind Lemma 8.
--
--   **Formalization Note** The zeros are taken over $\mathbb C$; the log-derivatives are written through the partial derivatives of $f$.
--
--   Differences from the source:
--   - encoding: log-derivatives ∂_s log f, ∂_t log f, ∂_s∂_t log f at (1, 1) → f_s/f, f_t/f and f_st/f − f_s f_t/f² with polynomial partial derivatives evaluated at (1, 1); reason: log f is smooth near (1, 1) since f(1, 1) > 0; same values
--   - encoding: a polynomial f(s, t) with no zeros with Re s, Re t > 0 → f : MvPolynomial (Fin 2) ℝ, zeros over ℂ through aeval; reason: Lean convention; same polynomials
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Lemma 7, p.7 (proof in A.5, p.13)

import Mathlib

namespace MaxEntOCRS

/-- Lemma 7 (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.7; A.5, p.13): let `f(s, t)` be a polynomial with nonnegative coefficients,
`f(1, 1) > 0`, and no zeros with `Re s, Re t > 0`. Then at `(1, 1)`,
`−∂_s∂_t log f ≤ ¼ (∂_s + ∂_t) log f`.

**Formalization Note** `f` is a real bivariate `MvPolynomial (Fin 2) ℝ` (variable `0 = s`,
`1 = t`), its zeros are taken over `ℂ` through `aeval`, and the log-derivatives at `(1, 1)` are
written through `f`'s partial derivatives: `∂_s log f = f_s/f`, `∂_t log f = f_t/f`,
`∂_s∂_t log f = f_st/f − f_s f_t/f²`, all evaluated at `(1, 1)` (`log f` is smooth there since
`f(1, 1) > 0`). -/
theorem lemma_7 (f : MvPolynomial (Fin 2) ℝ) (hcoeff : ∀ m, 0 ≤ f.coeff m)
    (hpos : 0 < MvPolynomial.eval (fun _ => (1 : ℝ)) f)
    (hzero : ∀ s t : ℂ, 0 < s.re → 0 < t.re → MvPolynomial.aeval ![s, t] f ≠ 0) :
    -(MvPolynomial.eval (fun _ => (1 : ℝ)) (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 f)) /
          MvPolynomial.eval (fun _ => (1 : ℝ)) f -
        MvPolynomial.eval (fun _ => (1 : ℝ)) (MvPolynomial.pderiv 0 f) *
            MvPolynomial.eval (fun _ => (1 : ℝ)) (MvPolynomial.pderiv 1 f) /
          MvPolynomial.eval (fun _ => (1 : ℝ)) f ^ 2) ≤
      1 / 4 * (MvPolynomial.eval (fun _ => (1 : ℝ)) (MvPolynomial.pderiv 0 f) /
            MvPolynomial.eval (fun _ => (1 : ℝ)) f +
          MvPolynomial.eval (fun _ => (1 : ℝ)) (MvPolynomial.pderiv 1 f) /
            MvPolynomial.eval (fun _ => (1 : ℝ)) f) := by sorry

end MaxEntOCRS
