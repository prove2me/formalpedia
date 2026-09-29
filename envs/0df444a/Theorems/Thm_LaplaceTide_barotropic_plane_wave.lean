-- Prove2me | Theorems.Thm_LaplaceTide_barotropic_plane_wave
-- name    : LaplaceTide.barotropic_plane_wave
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:33:40.214977+00:00
-- url     : https://prove2.me/theorems/a10bf5c8-47b0-4a06-92a2-a2240f356b81
-- title:
--   Barotropic mode: $\sigma = \pm k\sqrt{gD_*}$
-- statement:
--   **The barotropic (external) mode and its dispersion relation.**
--
--   For the zeroth normal mode the motion is depth independent. Dropping rotation ($f=0$) and all
--   $y$-dependence, the constant-depth tidal equations reduce to the pair
--
--   $$ U_t = -g Z_x, \qquad Z_t + D_* U_x = 0, $$
--
--   for the surface displacement $Z(x,t)$ and the horizontal velocity $U(x,t)$ over an ocean of
--   depth $D_*$. The lecture's plane-wave solution is
--
--   $$ Z(x,t) = a\,e^{\mathrm{i}(kx-\sigma t)}, \qquad
--      U(x,t) = a\,\frac{gk}{\sigma}\,e^{\mathrm{i}(kx-\sigma t)}, \qquad
--      \sigma = \pm k\sqrt{gD_*}. $$
--
--   The statement asserts the exact equivalence: for a nonzero amplitude $a$ and a nonzero
--   frequency $\sigma$, the pair $(Z,U)$ above solves both equations *if and only if*
--   $\sigma = k\sqrt{gD_*}$ or $\sigma = -k\sqrt{gD_*}$.
--
--   The first of the two equations holds identically for this pair, so the dispersion relation is
--   exactly the content of the continuity equation; it is the relation that gives the phase speed
--   $c_0 = \sqrt{gD_*}$ of the barotropic tide, about $200\ \mathrm{m\,s^{-1}}$ for a $4$ km ocean,
--   and hence its semidiurnal wavelength of some $8600$ km.
--
--   **Formalization Note** $Z$ and $U$ are complex-valued functions of two real variables, and the
--   derivatives are taken in one real variable at a time with the other held fixed, matching the
--   partial derivatives $Z_x$, $Z_t$, $U_x$, $U_t$ of the notes.
-- source:
--   M. Hendershott, Lecture 3: Solutions to Laplace's Tidal Equations, Woods Hole Oceanographic Institution GFD Program lecture notes, notes by V. Birman and E. Williams Frajka, pp. 34-44, https://www.whoi.edu/cms/files/lecture03_21374.pdf, p. 35, section 2.1 (barotropic solution, n = 0)

import Mathlib

namespace LaplaceTide

theorem barotropic_plane_wave (g Dstar a k sigma : ℝ) (Z U : ℝ → ℝ → ℂ)
    (hg : 0 < g) (hDstar : 0 < Dstar) (ha : a ≠ 0) (hsigma : sigma ≠ 0)
    (hZ : ∀ x t, Z x t = (a : ℂ) * Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * t)))
    (hU : ∀ x t, U x t = (a : ℂ) * ((g * k / sigma : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * t))) :
    ((∀ x t, deriv (fun s => U x s) t = -(g : ℂ) * deriv (fun s => Z s t) x) ∧
      (∀ x t, deriv (fun s => Z x s) t + (Dstar : ℂ) * deriv (fun s => U s t) x = 0)) ↔
      (sigma = k * Real.sqrt (g * Dstar) ∨ sigma = -(k * Real.sqrt (g * Dstar))) := by sorry

end LaplaceTide
