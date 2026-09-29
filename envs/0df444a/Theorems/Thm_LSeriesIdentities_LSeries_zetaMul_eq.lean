-- Prove2me | Theorems.Thm_LSeriesIdentities_LSeries_zetaMul_eq
-- name    : LSeriesIdentities.LSeries_zetaMul_eq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T12:07:47.853264+00:00
-- url     : https://prove2.me/theorems/7831118a-be95-4cfe-b851-fff9b1f15477
-- title:
--   The $L$-series of $\zeta \star \chi$ equals $\zeta(s)L(s,\chi)$
-- statement:
--   **The $L$-series of $\zeta \star \chi$ factors as $\zeta \cdot L(\chi)$.**
--
--   For a Dirichlet character $\chi$ modulo $N$, let $\zeta \star \chi$ denote the Dirichlet
--   convolution of the constant arithmetic function $1$ with $\chi$, that is
--
--   $$(\zeta \star \chi)(n) \;=\; \sum_{d \mid n} \chi(d).$$
--
--   Then in the half-plane of absolute convergence $\Re s > 1$ its Dirichlet series factors:
--
--   $$\sum_{n \ge 1} \frac{(\zeta\star\chi)(n)}{n^{s}} \;=\; \zeta(s)\,L(s,\chi).$$
--
--   This is the analytic shadow of the fact that the Dirichlet series of a convolution is the
--   product of the Dirichlet series — the ring homomorphism from arithmetic functions under
--   convolution to Dirichlet series under multiplication.
--
--   Its importance is that the coefficients of the product are **non-negative** when $\chi$ is a
--   real (quadratic) character, since $\sum_{d\mid n}\chi(d) \ge 0$ for every $n$. That
--   non-negativity is the engine of Landau's argument for the non-vanishing of $L(1,\chi)$ for
--   quadratic $\chi$, and hence of the absence of Siegel zeros in the simplest treatments — one
--   argues that if $L(1,\chi)$ vanished, the pole of $\zeta$ would cancel and the product would be
--   entire, contradicting a growth property forced by non-negative coefficients.
--
--   **Formalization note.** `DirichletCharacter.zetaMul χ` is Mathlib's name for the arithmetic
--   function $\zeta \star \chi$; it is coerced into $\mathbb{N} \to \mathbb{C}$ to form the
--   `LSeries`. `χ.LFunction` is the analytically continued Dirichlet $L$-function, which on
--   $\Re s > 1$ agrees with the $L$-series.
-- source:
--   Classical; see Montgomery & Vaughan, *Multiplicative Number Theory I*, §4.3, and Iwaniec & Kowalski, *Analytic Number Theory*, §5.9 (Landau's non-vanishing argument). Lean proof extracted from `Salt/SW/FourFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace LSeriesIdentities

open DirichletCharacter in
theorem LSeries_zetaMul_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n => (χ.zetaMul n : ℂ)) s = riemannZeta s * χ.LFunction s := by sorry

end LSeriesIdentities
