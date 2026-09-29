-- Prove2me | Theorems.Thm_Mandelbrot_mandelbrot_escape_criterion
-- name    : Mandelbrot.mandelbrot_escape_criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T01:52:04.839371+00:00
-- url     : https://prove2.me/theorems/7a2e2215-2208-4131-abe5-e5ec045184e9
-- title:
--   Escape criterion: $M = \{c : \forall k,\ |f_c^k(0)| \le 2\}$
-- statement:
--   **Escape criterion.** A parameter $c$ belongs to the Mandelbrot set if and only if the whole critical orbit stays in the closed disk of radius $2$:
--
--   $$c \in M \iff \forall k \in \mathbb{N},\ \left| f_c^{\,k}(0) \right| \le 2, \qquad f_c(z) = z^{2} + c.$$
--
--   Once the orbit of $0$ leaves the disk of radius $2$ it escapes to infinity. This classical fact is what makes $M$ compact and is the basis of every algorithm that draws it; formally, it replaces the filter-theoretic definition of non-escape by an explicit uniform bound.
-- source:
--   https://en.wikipedia.org/wiki/Mandelbrot_set#Basic_properties

import Definitions.Def_mandelbrot_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- The Mandelbrot set is exactly the set of parameters `c` whose critical orbit stays in
the closed disk of radius `2`. -/
theorem mandelbrot_escape_criterion :
    mandelbrotSet = {c : ℂ | ∀ k : ℕ, ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by sorry

end Mandelbrot
