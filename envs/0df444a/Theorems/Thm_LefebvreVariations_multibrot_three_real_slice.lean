-- Prove2me | Theorems.Thm_LefebvreVariations_multibrot_three_real_slice
-- name    : LefebvreVariations.multibrot_three_real_slice
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:45:06.719098+00:00
-- url     : https://prove2.me/theorems/38b0990e-fc0d-4b89-b6fe-4d354e5df00b
-- title:
--   Lefebvre's variations, No. 29 — on a theme by Douady and Hubbard: the real slice of the cubic Multibrot set
-- statement:
--   This is the real slice of the cubic Multibrot set.
--
--   Let $M_3$ be the set of $c\in\mathbb C$ for which the orbit of $0$ under $z\mapsto z^3+c$ does not tend to infinity. Then
--
--   $$
--   M_3\cap\mathbb R=\Big[-\frac{2}{3\sqrt3},\ \frac{2}{3\sqrt3}\Big].
--   $$
--
--   For $0\le c\le\frac2{3\sqrt3}$ the interval $|z|\le\frac1{\sqrt3}$ is invariant, since $z^3-z+\frac2{3\sqrt3}=(z-\frac1{\sqrt3})^2(z+\frac2{\sqrt3})\ge0$ for $z\ge0$; for $c>\frac2{3\sqrt3}$ the real orbit increases by at least $c-\frac2{3\sqrt3}$ at each step; negative parameters follow by the symmetry $z\mapsto-z$, which conjugates $z^3+c$ to $z^3-c$.
--
--   This is the cubic counterpart of the real slice $[-2,\frac14]$ of the Mandelbrot set; local connectivity of the Multibrot sets is open.
--
--   **Formalization Note** Membership uses the mission's `Mandelbrot.multibrotSet 3`, and a real parameter $x$ is identified with $(x:\mathbb C)$.
--
--   **Why this is a variation.** This varies the open problem on the local connectivity of the Multibrot sets (`Mandelbrot.multibrot_locally_connected`, in the Douady–Hubbard theme). It is the real-axis slice of the cubic Multibrot set $M_3$, computed exactly as the symmetric interval $[-2/(3\sqrt3),\,2/(3\sqrt3)]$; it is a special case of the parent set at $n=3$, not the full statement. Knowing exactly where $M_3$ meets the real line pins down explicit boundary points of the set whose local connectivity is the question.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Elementary escape estimates for unicritical polynomials z^n + c: J. Milnor, Dynamics in One Complex Variable, 3rd ed., Princeton Univ. Press, 2006; R. L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd ed., Addison-Wesley, 1989, Chapter 1 (real families x ↦ x² + c, analogous interval). Parent problem: Mandelbrot.multibrot_locally_connected.

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric

namespace LefebvreVariations

/-- **The real slice of the cubic Multibrot set** is the symmetric interval
`[-2/(3√3), 2/(3√3)]`: the orbit of `0` under `z ↦ z³ + c` (`c` real) stays bounded exactly when
`z ↦ z³ + c` has a real fixed point on the monotone side, i.e. `|c| ≤ max_z (z - z³) = 2/(3√3)`
(odd symmetry `f_{-c}(-z) = -f_c(z)` gives the other half). Reference: Devaney,
*An Introduction to Chaotic Dynamical Systems*, 2nd ed., Addison-Wesley 1989, §1.4 (the real
quadratic family, whose endpoint `1/4` is the same fixed-point tangency); the cubic family is the
`n = 3` case of the Multibrot sets of Milnor, *Dynamics in One Complex Variable*, 3rd ed.,
Princeton 2006, §8. It is the real part of the set whose local connectivity is
`Mandelbrot.multibrot_locally_connected` at `n = 3`. -/
theorem multibrot_three_real_slice :
    {x : ℝ | (x : ℂ) ∈ Mandelbrot.multibrotSet 3} =
      Set.Icc (-(2 / (3 * Real.sqrt 3))) (2 / (3 * Real.sqrt 3)) := by
  sorry

end LefebvreVariations
