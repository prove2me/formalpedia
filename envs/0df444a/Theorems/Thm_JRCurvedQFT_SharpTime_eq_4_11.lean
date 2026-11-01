-- Prove2me | Theorems.Thm_JRCurvedQFT_SharpTime_eq_4_11
-- name    : JRCurvedQFT.SharpTime.eq_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:35:43.322984+00:00
-- url     : https://prove2.me/theorems/c08c9ef2-052a-43e2-9d24-4a56c3a166e7
-- title:
--   Eq. (4.11) — $\int_{\mathbb R}\frac{e^{iE\tau}}{E^2+\lambda^2}\,dE=\frac{\pi e^{-|\tau|\lambda}}{\lambda}$
-- statement:
--   For every $\lambda>0$ and every real $\tau$,
--   $$\int_{-\infty}^{\infty}\frac{e^{iE\tau}}{E^2+\lambda^2}\,dE=\frac{\pi\,e^{-|\tau|\lambda}}{\lambda}.$$
--   The integrand is absolutely integrable. In the proof of Theorem 4.3 this identity, applied in the spectral decomposition of $\omega$, turns the partial Fourier transform in time into the factor $e^{-|t-s|\omega}/(2\omega)$.
--
--   Differences from the source: none.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, proof of Theorem 4.3, Eq. (4.11), p. 24

import Mathlib

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- **Eq. (4.11).** For `λ > 0` and real `τ`, `∫_ℝ e^{iEτ} / (E² + λ²) dE = π e^{−|τ|λ} / λ`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, proof of Theorem 4.3, Eq. (4.11), p. 24: "For λ > 0, ∫ e^{iEτ}/(E² + λ²) dE =
πe^{−|τ|λ}/λ."

**Formalization Note** The integral is the Bochner integral over `E ∈ ℝ` of a complex function
(absolutely integrable). -/
theorem eq_4_11 (lam : ℝ) (hlam : 0 < lam) (τ : ℝ) :
    ∫ E : ℝ, Complex.exp (Complex.I * E * τ) / ((E : ℂ) ^ 2 + (lam : ℂ) ^ 2)
      = (Real.pi * Real.exp (-(|τ| * lam)) / lam : ℝ) := by sorry

end JRCurvedQFT.SharpTime
