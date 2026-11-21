-- Prove2me | Theorems.Thm_MasulloGRH_sobolev_jet_haar_integrable_iff
-- name    : MasulloGRH.sobolev_jet_haar_integrable_iff
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:03:11.679178+00:00
-- url     : https://prove2.me/theorems/b813ad46-2667-4bf8-a4e8-02f3cba4e3a1
-- title:
--   Exact Sobolev jet threshold in positive-real Haar coordinates
-- statement:
--   For a nonnegative integer $m$ and any real $s$, the logarithmic jet weight is integrable on the positive real multiplicative group with respect to $dt/t$ exactly when
--
--   $$\int_0^\infty \frac{(\log t)^{2m}}{(1+(\log t)^2)^{s/2}}\,\frac{dt}{t}<\infty\quad\Longleftrightarrow\quad 2m+1<s.$$
--
--   This is the positive-real coordinate calculation in Lemma 9.1.2.4 and Proposition 9.1.2.5. It includes the nonintegrable boundary and all real orders, not only $s>1$. The case $m=0$ gives the scalar integrability threshold $s>1$ used in the weighted Cauchy–Schwarz estimate of Proposition 9.1.2.6.
--
--   Formalization Note: the integrand contains the density $t^{-1}$ and is integrated over $(0,\infty)$ against Lebesgue measure. The result does not assert the quotient-integration step for a general modulated group.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, p. 402, Lemma 9.1.2.4 (logarithmic substitution for Haar measure dt/t) and Proposition 9.1.2.5, equations (9.1.2.15)–(9.1.2.16), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. This formalizes the positive-real Haar-coordinate integral, with the valid extension to arbitrary real s.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem MasulloGRH.sobolev_jet_haar_integrable_iff (m : ℕ) (s : ℝ)  :
    IntegrableOn (fun t : ℝ => t⁻¹ *
      ((Real.log t) ^ (2 * m) / (1 + (Real.log t) ^ 2) ^ (s / 2))) (Ioi 0) ↔
      2 * (m : ℝ) + 1 < s := by sorry
