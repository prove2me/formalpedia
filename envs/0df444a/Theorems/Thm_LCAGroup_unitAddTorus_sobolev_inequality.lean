-- Prove2me | Theorems.Thm_LCAGroup_unitAddTorus_sobolev_inequality
-- name    : LCAGroup.unitAddTorus_sobolev_inequality
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:00:40.182437+00:00
-- url     : https://prove2.me/theorems/35dffe6e-7ff8-4c48-bffa-1418d97e3649
-- title:
--   Sobolev inequality on the torus: $\sup_{\mathbb T^n}|\varphi|\le C\,\|\varphi\|_s$ for $s>n/2$, where $\|\varphi\|_s^2=\sum_{\xi\in\mathbb Z^n}(1+|\xi|^2)^s|\widehat\varphi(\xi)|^2$
-- statement:
--   **Sobolev inequality on the torus $\mathbb T^n$** (eq. (D.1.10.11) in Example D.1.10.4 of the source, recalled from Warner's book).
--
--   Let $n\ge 0$ and $\mathbb T^n=(\mathbb R/\mathbb Z)^n$ with its Haar measure $dz$ of total mass $1$. For a continuous function $\varphi\colon\mathbb T^n\to\mathbb C$ and $\xi\in\mathbb Z^n$ let
--   $$\widehat\varphi(\xi)=\int_{\mathbb T^n}\varphi(z)\,e^{-2\pi i\,\xi\cdot z}\,dz$$
--   be the Fourier coefficients of $\varphi$, and for a real number $s$ let
--   $$\|\varphi\|_s^2=\sum_{\xi\in\mathbb Z^n}(1+|\xi|^2)^s\,|\widehat\varphi(\xi)|^2\ \in[0,+\infty],\qquad |\xi|^2=\xi_1^2+\dots+\xi_n^2,$$
--   be the square of the Sobolev norm of order $s$ of $\varphi$.
--
--   **Statement.** If $s>n/2$, there is a constant $C$, depending only on $n$ and $s$, such that for every continuous $\varphi\colon\mathbb T^n\to\mathbb C$
--   $$\sup_{z\in\mathbb T^n}|\varphi(z)|\ \le\ C\,\|\varphi\|_s .$$
--   In particular this holds for every $\varphi\in C^\infty(\mathbb T^n)$, for which $\|\varphi\|_s<\infty$ for all $s$.
--
--   The inequality is the basic Sobolev embedding $H^s(\mathbb T^n)\hookrightarrow C(\mathbb T^n)$ for $s>n/2$. The source uses it to show that for each $1\le p<\infty$ the seminorms $\|\partial_z^\beta f\|_{L^p(\mathbb T^n)}$, $\beta\in\mathbb N^n$, define the same topology on $C^\infty(\mathbb T^n)=\mathcal S(\mathbb T^n)$ as the seminorms $\sup_z|\partial_z^\beta f(z)|$ (Example D.1.10.4).
--
--   **Formalization Note.** $\mathbb T^n$ is Mathlib's `UnitAddTorus (Fin n)` and $\widehat\varphi(\xi)$ is `UnitAddTorus.mFourierCoeff φ ξ` (integration against the product of the probability Haar measures). The inequality is stated in squared form with values in $[0,\infty]$: there is `C : ℝ≥0` with `‖φ z‖ₑ ^ 2 ≤ C * ∑' ξ, ENNReal.ofReal ((1 + ∑ i, (ξ i)^2) ^ s) * ‖mFourierCoeff φ ξ‖ₑ ^ 2` for all `φ : C(UnitAddTorus (Fin n), ℂ)` and all `z`; the constant `C` of the Lean statement is the square of the constant of the displayed inequality, and the sum is an unconditional sum in `ℝ≥0∞`, so that no summability hypothesis is needed. **Deviation from the source.** The source states the inequality for an integer $s>n/2$ and for $\varphi\in C^\infty(\mathbb T^n)$; here $s$ is any real number $>n/2$ and $\varphi$ is any continuous function (with $\|\varphi\|_s=+\infty$ allowed), which is the same classical inequality in its usual generality and contains the source's statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 786, Example D.1.10.4, eq. (D.1.10.11); classical reference (as cited in the source): F. W. Warner, Foundations of Differentiable Manifolds and Lie Groups, Springer-Verlag, 1983, Corollary (b) to 6.22

import Mathlib

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal

set_option autoImplicit false

namespace LCAGroup

theorem unitAddTorus_sobolev_inequality (n : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 < s) :
    ∃ C : ℝ≥0, ∀ (φ : C(UnitAddTorus (Fin n), ℂ)) (z : UnitAddTorus (Fin n)),
      ‖φ z‖ₑ ^ 2 ≤ C * ∑' ξ : Fin n → ℤ,
        ENNReal.ofReal ((1 + ∑ i, (ξ i : ℝ) ^ 2) ^ s) * ‖mFourierCoeff (⇑φ) ξ‖ₑ ^ 2 := by sorry

end LCAGroup
