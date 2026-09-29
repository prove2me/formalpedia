-- Prove2me | Theorems.Thm_LaplaceTide_vertical_structure_mode
-- name    : LaplaceTide.vertical_structure_mode
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:33:22.086243+00:00
-- url     : https://prove2.me/theorems/70ac7521-2cf2-4bd8-8697-1cbe59f20d8a
-- title:
--   Vertical structure equation and equivalent depth $D_n$
-- statement:
--   **Vertical structure equation and equivalent depth.**
--
--   Separating variables in the linear hydrostatic equations for a stratified ocean of depth
--   $D_*$ leaves, for each normal mode $n$, the vertical structure problem
--
--   $$ F_{wzz} + \frac{N^2}{g D_n} F_w = 0, $$
--
--   where $N$ is the buoyancy frequency and $D_n$ the *equivalent depth* of the mode,
--
--   $$ D_n = \frac{\left[\int_{-D_*}^{0} N(z')\,\mathrm{d}z'\right]^2}{g\,n^2\pi^2}. $$
--
--   For a constant buoyancy frequency $N > 0$ the numerator is $(N D_*)^2$. The statement asserts
--   that for every $g>0$, $D_*>0$, $N>0$ and every mode index $n \ge 1$, with
--
--   $$ D_n = \frac{(N D_*)^2}{g\,n^2\pi^2}, \qquad
--      F_w(z) = \sin\!\left(\frac{n\pi (z+D_*)}{D_*}\right), $$
--
--   the function $F_w$ satisfies the vertical structure equation at every depth $z$, and vanishes
--   at the bottom $z=-D_*$ and at the surface $z=0$.
--
--   Equivalently, the equivalent depth is exactly the eigenvalue for which the sine mode of
--   vertical wavenumber $n\pi/D_*$ solves the problem; this is what fixes the modal phase speeds
--   $c_n = \sqrt{gD_n} = N D_*/(n\pi)$ used in §2.2 of the notes.
--
--   **Formalization Note** The second derivative is the derivative of the derivative of $F_w$ as
--   a function of $z$. The upper boundary condition formalized here is the rigid-lid condition
--   $F_w(0)=0$; the free-surface condition $F_w - D_n F_{wz} = 0$ at $z=0$ quoted in the notes is
--   satisfied by these sine modes only in the limit of small equivalent depth, and is not claimed.
-- source:
--   M. Hendershott, Lecture 3: Solutions to Laplace's Tidal Equations, Woods Hole Oceanographic Institution GFD Program lecture notes, notes by V. Birman and E. Williams Frajka, pp. 34-44, https://www.whoi.edu/cms/files/lecture03_21374.pdf, p. 34, equation (4) and the formula for the equivalent depth $D_n$

import Mathlib

namespace LaplaceTide

theorem vertical_structure_mode (N Dstar g : ℝ) (n : ℕ) (Dn : ℝ) (Fw : ℝ → ℝ)
    (hN : 0 < N) (hDstar : 0 < Dstar) (hg : 0 < g) (hn : 1 ≤ n)
    (hDn : Dn = (N * Dstar) ^ 2 / (g * (n : ℝ) ^ 2 * Real.pi ^ 2))
    (hFw : ∀ z, Fw z = Real.sin ((n : ℝ) * Real.pi * (z + Dstar) / Dstar)) :
    (∀ z, deriv (deriv Fw) z + (N ^ 2 / (g * Dn)) * Fw z = 0) ∧
      Fw (-Dstar) = 0 ∧ Fw 0 = 0 := by sorry

end LaplaceTide
