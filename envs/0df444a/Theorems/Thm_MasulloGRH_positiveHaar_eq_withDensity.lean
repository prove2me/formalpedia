-- Prove2me | Theorems.Thm_MasulloGRH_positiveHaar_eq_withDensity
-- name    : MasulloGRH.positiveHaar_eq_withDensity
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:16:17.510189+00:00
-- url     : https://prove2.me/theorems/f9f1e973-4f83-46ff-9b6a-540397d69611
-- title:
--   Exponential pushforward is the positive-real measure dt/t
-- statement:
--   Let $\lambda$ denote Lebesgue measure on $\mathbb R$. The pushforward of $\lambda$ by the exponential function is exactly the measure on the positive real axis with density $1/t$ relative to Lebesgue measure: $$\exp_*\lambda=(\lambda|_{(0,\infty)})(dt)/t.$$ Equivalently, for every nonnegative measurable $g$, $$\int_{\mathbb R}g(e^x)\,dx=\int_0^\infty g(t)\,\frac{dt}{t}.$$ This identifies the positive-real Haar coordinates used in the scalar Sobolev estimates. Formalization Note: both measures are represented on the ambient real line; the right-hand side restricts Lebesgue measure to the positive half-line before adding the density.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, p. 402, proof of Lemma 9.1.2.4, positive-real normalized Haar measure dt/t and logarithmic change of variables. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. This is the measure-theoretic coordinate identity underlying that calculation, not the general compact-fiber reduction.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem MasulloGRH.positiveHaar_eq_withDensity :
    Measure.map Real.exp (volume : Measure ℝ) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal t⁻¹) := by sorry
