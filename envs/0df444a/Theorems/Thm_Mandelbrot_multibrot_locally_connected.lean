-- Prove2me | Theorems.Thm_Mandelbrot_multibrot_locally_connected
-- name    : Mandelbrot.multibrot_locally_connected
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T02:20:59.587746+00:00
-- url     : https://prove2.me/theorems/3f01e413-30f9-4a5a-8416-4658d33ce6d3
-- title:
--   MLC for all Multibrot sets
-- statement:
--   **Conjecture (MLC for Multibrot sets).** For every $n$, the Multibrot set $M_n$ of the family $z \mapsto z^{n} + c$ is locally connected.
--
--   This strengthens MLC from the quadratic family to all unicritical degrees. No restriction on $n$ is needed: for $n = 0$ the map $z \mapsto 1 + c$ is constant and for $n = 1$ it is a translation, and in both degenerate cases the resulting parameter set is locally connected for elementary reasons.
-- source:
--   https://en.wikipedia.org/wiki/Multibrot_set

import Definitions.Def_mandelbrot_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- The MLC conjecture for the whole unicritical family: every Multibrot set is locally
connected. The degenerate exponents `n = 0` and `n = 1` need not be excluded. -/
theorem multibrot_locally_connected (n : ℕ) : LocallyConnectedSpace (multibrotSet n) := by
  sorry

end Mandelbrot
