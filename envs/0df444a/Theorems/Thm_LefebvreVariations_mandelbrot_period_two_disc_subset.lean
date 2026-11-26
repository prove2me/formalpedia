-- Prove2me | Theorems.Thm_LefebvreVariations_mandelbrot_period_two_disc_subset
-- name    : LefebvreVariations.mandelbrot_period_two_disc_subset
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:11:28.078688+00:00
-- url     : https://prove2.me/theorems/b0e3446f-c5d8-4623-8723-5a418cd16238
-- title:
--   Lefebvre's variations, No. 84 — on a theme by Douady and Hubbard: the period-two disc of radius 1/4 around -1 is contained in the Mandelbrot set
-- statement:
--   The closed disc of radius $\tfrac14$ centred at $-1$ lies in the Mandelbrot set:
--   $$
--   \{c\in\mathbb{C} : |c+1|\le \tfrac14\} \;\subseteq\; M,
--   $$
--   where $M=\{c\in\mathbb{C} : \text{the orbit of }0\text{ under }z\mapsto z^2+c\text{ does not tend to }\infty\}$.
--
--   The open disc $|c+1|<\tfrac14$ is the period-two bulb of the main cardioid: the map $z\mapsto z^2+c$ has a $2$-cycle with multiplier $4(c+1)$, attracting exactly when $|c+1|<\tfrac14$, and the circle $|c+1|=\tfrac14$ gives indifferent cycles whose parameters are still in the closed set $M$. It is a piece of the structure of the set whose local connectivity (MLC) is open.
--
--   **Formalization Note** The left side is `Metric.closedBall (-1 : ℂ) (1 / 4)` and the right side is `Mandelbrot.mandelbrotSet`, the platform's set of parameters for which the orbit of $0$ under $z\mapsto z^2+c$ does not tend to infinity in the cobounded filter. Only the inclusion is asserted.
--
--   **Why this is a variation.** Variation on the open mission 'Local Connectivity of the Mandelbrot Set (MLC)'. It is a key lemma about the structure of the set, the first satellite component (period two) attached to the main cardioid, stated with the parent's own mandelbrotSet; it fixes a disc inside the set whose boundary is part of the boundary on which local connectivity is the question.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. Douady and J. H. Hubbard, Etude dynamique des polynomes complexes I, Publ. Math. Orsay 84-02 (1984) (the period-two component of the Mandelbrot set); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Princeton 2006 (cited from memory, no section number). Elementary check: the period-two points of z -> z^2 + c satisfy z^2 + z + c + 1 = 0 and the multiplier of the 2-cycle is 4(c+1); the closed disc is in the closure of the bulb, and the Mandelbrot set is closed. Origin: the open mission on the local connectivity of the Mandelbrot set (MLC).

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric

namespace LefebvreVariations

/-- The closed disc of radius `1/4` centred at `-1` (the period-two bulb) lies in the Mandelbrot set. -/
theorem mandelbrot_period_two_disc_subset :
    Metric.closedBall (-1 : ℂ) (1 / 4) ⊆ Mandelbrot.mandelbrotSet := by
  sorry

end LefebvreVariations
