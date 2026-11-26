-- Prove2me | Theorems.Thm_LefebvreVariations_multibrot_five_real_slice
-- name    : LefebvreVariations.multibrot_five_real_slice
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:09:27.696008+00:00
-- url     : https://prove2.me/theorems/787a9460-4774-5dc7-8cae-fdd24c33f4ee
-- title:
--   Lefebvre's variations, No. 72 — on a theme by Douady and Hubbard: the real slice of the quintic Multibrot set is a symmetric interval
-- statement:
--   Let $M_5=\{c\in\mathbb{C} : \text{the orbit of }0\text{ under }z\mapsto z^5+c\text{ does not tend to }\infty\}$ be the quintic Multibrot set. Its intersection with the real axis is
--   $$
--   M_5\cap\mathbb{R} \;=\; \Bigl[-\frac{4}{5^{5/4}},\ \frac{4}{5^{5/4}}\Bigr] \;\approx\; [-0.5350,\ 0.5350].
--   $$
--
--   For odd $n$ the map $z\mapsto z^n+c$ satisfies $f_{-c}(-z)=-f_c(z)$, so the real slice is symmetric, and its endpoint $(n-1)/n^{n/(n-1)}$ is the saddle-node parameter of the real fixed point; for $n=3$ this is $2/(3\sqrt3)$ and the statement is the case $n=5$. It is the real part of the set whose local connectivity is the open problem of the mission on the Multibrot sets.
--
--   **Formalization Note** The set is $\{x:\mathbb{R}\mid (x:\mathbb{C})\in \texttt{multibrotSet}\ 5\}$, with the platform's definition (orbit of $0$ under $z\mapsto z^5+c$ does not tend to infinity in the cobounded filter of $\mathbb{C}$). The endpoints are written with real powers, `4 / (5:ℝ)^((5:ℝ)/4)` and its negative, and both belong to the set (closed interval `Set.Icc`).
--
--   **Why this is a variation.** Variation on the open mission on the Mandelbrot and Multibrot sets (local connectivity, Mandelbrot.multibrot_locally_connected). It is the real slice at the exponent n = 5, stated with the parent's own multibrotSet; the real slice is the first piece of the boundary one understands completely, and the proof (a fixed-point tangency plus odd symmetry) is a template for the next exponents.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   R. L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd ed., Addison-Wesley 1989, Sec. 1.4 (the real quadratic family; the tangency endpoint); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Princeton 2006, Sec. 8 (Multibrot sets), cited from memory. The statement itself is an elementary computation with the real fixed points of z -> z^5 + c, not a quotation; the endpoints were confirmed numerically by the author (orbit-boundedness scan on a grid of 250001 real parameters: boundary at 0.53502 against 4/5^(5/4) = 0.534992). Origin: the open mission on the local connectivity of the Multibrot sets (theorem Mandelbrot.multibrot_locally_connected).

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric

namespace LefebvreVariations

/-- The real slice of the quintic Multibrot set is `[-4/5^{5/4}, 4/5^{5/4}]`. -/
theorem multibrot_five_real_slice :
    {x : ℝ | (x : ℂ) ∈ Mandelbrot.multibrotSet 5} =
      Set.Icc (-(4 / (5 : ℝ) ^ ((5 : ℝ) / 4))) (4 / (5 : ℝ) ^ ((5 : ℝ) / 4)) := by
  sorry

end LefebvreVariations
