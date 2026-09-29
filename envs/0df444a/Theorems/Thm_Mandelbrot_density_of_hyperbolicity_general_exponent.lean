-- Prove2me | Theorems.Thm_Mandelbrot_density_of_hyperbolicity_general_exponent
-- name    : Mandelbrot.density_of_hyperbolicity_general_exponent
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T02:14:05.015801+00:00
-- url     : https://prove2.me/theorems/53b58d0e-5802-4ffc-b2f7-f441f7b9f804
-- title:
--   Density of hyperbolicity for Multibrot sets, $2 \le n$
-- statement:
--   **Conjecture.** For every $n \ge 2$, parameters with an attracting cycle are dense in the Multibrot set $M_n$ of the unicritical family $z \mapsto z^{n} + c$.
--
--   This is the degree-$n$ form of Fatou's conjecture. The hypothesis $n \ge 2$ is necessary: for $n = 1$ the family consists of translations, which have no attracting cycles at all, so the statement fails there.
-- source:
--   https://en.wikipedia.org/wiki/Multibrot_set

import Definitions.Def_mandelbrot_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- The density of hyperbolicity conjecture for the unicritical family `z ↦ z ^ n + c`
with `2 ≤ n`. -/
theorem density_of_hyperbolicity_general_exponent {n : ℕ} (hn : 2 ≤ n) :
    multibrotSet n ⊆ closure {c : ℂ | ∃ m z, IsAttractingCycle (fun z ↦ z ^ n + c) m z} := by
  sorry

end Mandelbrot
