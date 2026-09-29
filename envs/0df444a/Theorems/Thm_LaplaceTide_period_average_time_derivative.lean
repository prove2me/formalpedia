-- Prove2me | Theorems.Thm_LaplaceTide_period_average_time_derivative
-- name    : LaplaceTide.period_average_time_derivative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:34:32.546281+00:00
-- url     : https://prove2.me/theorems/c9ccffe3-9f8c-414c-9360-543844fddfa2
-- title:
--   Period average of a time derivative vanishes: $\langle KE_t\rangle = \langle PE_t\rangle = 0$
-- statement:
--   **Averaging over one tidal period.**
--
--   For a tide of period $T$ it is convenient to work with the average over one period, written
--   $\langle\,\cdot\,\rangle$. The statement records the elementary fact that underlies equation
--   (31) of the notes, $\langle KE_t\rangle = \langle PE_t\rangle = 0$: if an energy density
--   $E(t)$ is continuously differentiable and $T$-periodic, then
--
--   $$ \langle E_t \rangle \;=\; \frac{1}{T}\int_{0}^{T} E'(t)\,\mathrm{d}t \;=\; 0 . $$
--
--   Applied to the kinetic and potential energy densities of a periodic tide, this is what removes
--   the storage terms from the energy equation and leaves a balance between the flux divergence,
--   the work of the tide generating potential and the dissipation.
--
--   **Formalization Note** $E$ is assumed differentiable everywhere with continuous derivative,
--   and $T$-periodicity means $E(t+T)=E(t)$ for all $t$. The hypothesis $T>0$ records that $T$ is
--   the tidal period; the identity is proved without using it.
-- source:
--   M. Hendershott, Lecture 3: Solutions to Laplace's Tidal Equations, Woods Hole Oceanographic Institution GFD Program lecture notes, notes by V. Birman and E. Williams Frajka, pp. 34-44, https://www.whoi.edu/cms/files/lecture03_21374.pdf, p. 41, section 6, equation (31)

import Mathlib

namespace LaplaceTide

theorem period_average_time_derivative (T : ℝ) (E : ℝ → ℝ) (hT : 0 < T)
    (hdiff : Differentiable ℝ E) (hcont : Continuous (deriv E)) (hper : Function.Periodic E T) :
    (1 / T) * ∫ t in (0 : ℝ)..T, deriv E t = 0 := by sorry

end LaplaceTide
