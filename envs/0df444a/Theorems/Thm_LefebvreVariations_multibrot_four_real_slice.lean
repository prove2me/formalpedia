-- Prove2me | Theorems.Thm_LefebvreVariations_multibrot_four_real_slice
-- name    : LefebvreVariations.multibrot_four_real_slice
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:21:04.632797+00:00
-- url     : https://prove2.me/theorems/ca06e621-aafd-5f92-81f6-e39b2daf1eae
-- title:
--   Lefebvre's variations, No. 49 — on a theme by Douady and Hubbard: the real slice of the quartic Multibrot set
-- statement:
--   Let $M_4=\{c\in\mathbb{C} : \text{the orbit of }0\text{ under }z\mapsto z^4+c\text{ does not tend to }\infty\}$ be the quartic Multibrot set. Its intersection with the real axis is
--   $$
--   M_4\cap\mathbb{R} \;=\; \Bigl[-2^{1/3},\ \frac{3}{4^{4/3}}\Bigr] \;\approx\; [-1.2599,\ 0.4725].
--   $$
--
--   For $n=2$ the analogous two endpoints are $-2$ and $\tfrac14$, the real slice of the Mandelbrot set. For even $n$ the left endpoint $-2^{1/(n-1)}$ is the parameter at which the critical value $c$ lands on the repelling fixed point $-c$, and the right endpoint $(n-1)/n^{n/(n-1)}$ is the saddle-node (cusp) parameter of the positive fixed point; the statement is the case $n=4$. It is the real part of the set whose local connectivity is the open problem of the mission on the Multibrot sets.
--
--   **Formalization Note** The set is $\{x:\mathbb{R}\mid (x:\mathbb{C})\in \texttt{multibrotSet}\ 4\}$, with the platform's definition (orbit of $0$ under $z\mapsto z^4+c$ does not tend to infinity in the cobounded filter of $\mathbb{C}$). The endpoints are written with real powers: `(2:ℝ)^((1:ℝ)/3)` and `3/(4:ℝ)^((4:ℝ)/3)`; both endpoints belong to the set (closed interval `Set.Icc`).
--
--   **Why this is a variation.** This varies the open problem on the local connectivity of the Multibrot sets (`Mandelbrot.multibrot_locally_connected`, in the Douady–Hubbard theme, which at $n=2$ is the MLC question for the Mandelbrot set). It is the real-axis slice of the quartic Multibrot set $M_4$, computed exactly as the interval $[-2^{1/3},\,3/4^{4/3}]$; it is a special case, not the full open statement. Knowing exactly where $M_4$ meets the real line pins down its first boundary points and the shape of the set that the local connectivity question is about.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   R. L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd ed., Addison-Wesley 1989, section 1.4 (the real quadratic family z^2+c, with the exceptional parameters c = -2 and c = 1/4); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Princeton 2006, section 8 (Multibrot sets of z^n+c); the quartic real slice is the elementary computation with the real fixed points of z^4+c and is not quoted from either source (section numbers cited from memory). Origin of this statement: it is the real-axis case of the set in the open mission 'Local Connectivity of the Mandelbrot Set (MLC)' / Mandelbrot.multibrot_locally_connected at n = 4, companion of the variations on the real slices of M_2, M_3 and the inradius of M_n.

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric

namespace LefebvreVariations

/-- **The real slice of the quartic Multibrot set** is the interval
`[-2^{1/3}, 3/4^{4/3}]`: for `c` real the map `z ↦ z⁴ + c` is even, so the orbit of `0` stays
bounded exactly when `c` lies between the parameter at which the critical value `c` lands on the
repelling fixed point `-c` (`c⁴ = 2|c|`, i.e. `c = -2^{1/3}`) and the parameter of the saddle-node
tangency of the positive fixed point (`max_{z ≥ 0} (z - z⁴) = 3/4^{4/3}`, the case `n = 4` of the
inradius `(n-1)/n^{n/(n-1)}`). For `n = 2` the same two parameters are `-2` and `1/4`.
Reference: Devaney, *An Introduction to Chaotic Dynamical Systems*, 2nd ed., Addison-Wesley 1989,
§1.4 (the real quadratic family); the quartic family is the case `n = 4` of the Multibrot sets of
Milnor, *Dynamics in One Complex Variable*, 3rd ed., Princeton 2006, §8; the statement itself is
an elementary computation with the real fixed points, not a quotation. It is the real part of
the set whose local connectivity is `Mandelbrot.multibrot_locally_connected` at `n = 4`. -/
theorem multibrot_four_real_slice :
    {x : ℝ | (x : ℂ) ∈ Mandelbrot.multibrotSet 4} =
      Set.Icc (-((2 : ℝ) ^ ((1 : ℝ) / 3))) (3 / (4 : ℝ) ^ ((4 : ℝ) / 3)) := by
  sorry

end LefebvreVariations
