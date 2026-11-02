-- Prove2me | Theorems.Thm_Grothendieck_inv_series_radius
-- name    : Grothendieck.inv_series_radius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-02T04:17:34.937472+00:00
-- url     : https://prove2.me/theorems/aeedc812-9cf0-4774-8b3c-4b2a932d87eb
-- title:
--   Theorem 3.1 — the radius of convergence is at least $|E_r(i)|$
-- statement:
--   For every positive integer $r$, the Taylor series
--
--   $$
--   E_r^{-1}(t)=\sum_{k\ge0}b_{2k+1}t^{2k+1}
--   $$
--
--   has convergence radius at least $|E_r(i)|$: for every complex $z$ with
--
--   $$
--   |z|<|E_r(i)|
--   $$
--
--   the series $\sum_k b_{2k+1}z^{2k+1}$ converges.
--
--   This is the quantitative statement used in the rounding argument. The paper's proof combines Lemma 3.2, which bounds the radius from below by $c_r=\min_{t}|E_r(e^{it})|$, with Lemma 3.5, which identifies this minimum with $|E_r(i)|$ for $r\ge2$; for $r=1$ the series is $E_1^{-1}(t)=\sin(\frac\pi2t)$, whose Taylor series has infinite radius, so the statement holds trivially. The paper stresses that the case $r=2$ was known from Haagerup's work with the better radius $1$, and that its own argument gives a smaller but uniform radius for all $r\ge2$.
--
--   **Formalization Note** Convergence at every `z : ℂ` with `‖z‖ < ‖ErComplex r Complex.I‖` is stated as summability of `fun k => (invCoeff r (2*k+1) : ℂ) * z ^ (2*k+1)`.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, Theorem 3.1, p. 88. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Series

namespace Grothendieck

theorem inv_series_radius (r : ℕ) (hr : 1 ≤ r) (z : ℂ)
    (hz : ‖z‖ < ‖ErComplex r Complex.I‖) :
    Summable fun k : ℕ => (invCoeff r (2 * k + 1) : ℂ) * z ^ (2 * k + 1) := by sorry

end Grothendieck
