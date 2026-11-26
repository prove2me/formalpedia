-- Prove2me | Theorems.Thm_LefebvreVariations_multibrot_six_real_slice
-- name    : LefebvreVariations.multibrot_six_real_slice
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:10:14.649772+00:00
-- url     : https://prove2.me/theorems/8df37e53-dcb2-4a0b-953a-ac26e510ff05
-- title:
--   Lefebvre's variations, No. 82 — on a theme by Douady and Hubbard: the real slice of the sextic Multibrot set is the interval from -2^(1/5) to 5/6^(6/5)
-- statement:
--   Let $M_6=\{c\in\mathbb{C} : \text{the orbit of }0\text{ under }z\mapsto z^6+c\text{ does not tend to }\infty\}$ be the sextic Multibrot set. Its intersection with the real axis is
--   $$
--   M_6\cap\mathbb{R} \;=\; \Bigl[-2^{1/5},\ \frac{5}{6^{6/5}}\Bigr] \;\approx\; [-1.1487,\ 0.5824].
--   $$
--
--   For even $n$ the left endpoint $-2^{1/(n-1)}$ is the parameter at which the critical value $c$ lands on the repelling fixed point $-c$, and the right endpoint $(n-1)/n^{n/(n-1)}$ is the saddle-node parameter of the positive fixed point; for $n=2$ they are $-2$ and $\tfrac14$, and the statement is the case $n=6$. It is the real part of the set whose local connectivity is the open problem of the mission on the Multibrot sets.
--
--   **Formalization Note** The set is $\{x:\mathbb{R}\mid (x:\mathbb{C})\in \texttt{multibrotSet}\ 6\}$, with the platform's definition (orbit of $0$ under $z\mapsto z^6+c$ does not tend to infinity in the cobounded filter of $\mathbb{C}$). The endpoints are `-((2:ℝ)^((1:ℝ)/5))` and `5/(6:ℝ)^((6:ℝ)/5)`, and both belong to the set (closed interval `Set.Icc`).
--
--   **Why this is a variation.** Variation on the open mission on the Mandelbrot and Multibrot sets (local connectivity, Mandelbrot.multibrot_locally_connected). It is the real slice at the exponent n = 6, stated with the parent's own multibrotSet, the next even case after the quartic one; the endpoints come from a fixed-point tangency and a critical-orbit landing on a repelling fixed point, a template for all even exponents.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   R. L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd ed., Addison-Wesley 1989, Sec. 1.4 (the real quadratic family); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Princeton 2006, Sec. 8 (Multibrot sets), cited from memory. The statement itself is an elementary computation with the real fixed points of z -> z^6 + c, not a quotation; the endpoints were confirmed numerically by the author (orbit-boundedness scan: real boundary at -1.14869 and 0.58238 against -2^(1/5) = -1.148698 and 5/6^(6/5) = 0.582356). Origin: the open mission on the local connectivity of the Multibrot sets (theorem Mandelbrot.multibrot_locally_connected).

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric

namespace LefebvreVariations

/-- The real slice of the sextic Multibrot set is `[-2^{1/5}, 5/6^{6/5}]`. -/
theorem multibrot_six_real_slice :
    {x : ℝ | (x : ℂ) ∈ Mandelbrot.multibrotSet 6} =
      Set.Icc (-((2 : ℝ) ^ ((1 : ℝ) / 5))) (5 / (6 : ℝ) ^ ((6 : ℝ) / 5)) := by
  sorry

end LefebvreVariations
