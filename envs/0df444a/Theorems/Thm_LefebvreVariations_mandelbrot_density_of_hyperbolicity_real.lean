-- Prove2me | Theorems.Thm_LefebvreVariations_mandelbrot_density_of_hyperbolicity_real
-- name    : LefebvreVariations.mandelbrot_density_of_hyperbolicity_real
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:17:46.841675+00:00
-- url     : https://prove2.me/theorems/c1dc79ca-6a54-58ed-b610-f56a3a286c7b
-- title:
--   Lefebvre's variations, No. 185 — on a theme by Douady and Hubbard: hyperbolic parameters are dense in the real slice of the Mandelbrot set
-- statement:
--   Every real number $c\in[-2,\tfrac14]$ is a limit of complex parameters $c_j$ for which $z\mapsto z^2+c_j$ has an attracting cycle, that is, a point $z$ and an $m\ge1$ with $f^{\circ m}(z)=z$ and $|(f^{\circ m})'(z)|<1$:
--   $$
--   [-2,\tfrac14]\ \subseteq\ \overline{\{\,c\in\mathbb{C}:\ z\mapsto z^2+c \text{ has an attracting cycle}\,\}} .
--   $$
--
--   The parent (density of hyperbolicity in the quadratic family) is open for the full Mandelbrot set. Restricted to the real parameters, which are exactly $M\cap\mathbb{R}=[-2,\tfrac14]$, it is a theorem: density of hyperbolicity in the real quadratic (logistic) family, due to Lyubich and to Graczyk and Swiatek.
--
--   **Formalization Note** The attracting-cycle condition is `Mandelbrot.IsAttractingCycle` exactly as in the parent (`0 < n`, periodic point, differentiable, multiplier of modulus $<1$). The left side is the image of $[-2,1/4]\subset\mathbb{R}$ in $\mathbb{C}$, and the closure is taken in $\mathbb{C}$, as in the parent.
--
--   **Why this is a variation.** Variation on the open platform theorem Mandelbrot.density_of_hyperbolicity: the parent's conclusion for the real parameters [-2, 1/4], the one slice where the conjecture is a known theorem. It uses the parent's own predicate IsAttractingCycle and closure in the complex plane.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   M. Lyubich, Dynamics of quadratic polynomials I-II, Acta Math. 178 (1997), 185-297; J. Graczyk and G. Swiatek, Generic hyperbolicity in the logistic family, Ann. of Math. 146 (1997), 1-52 (both cited from memory, titles/journals/years not re-checked online). That M intersect R = [-2, 1/4] is the platform theorem LefebvreVariations.mandelbrot_real_slice. Origin: platform theorem Mandelbrot.density_of_hyperbolicity.

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace LefebvreVariations

theorem mandelbrot_density_of_hyperbolicity_real :
    (fun x : ℝ ↦ (x : ℂ)) '' Set.Icc (-2 : ℝ) (1 / 4) ⊆
      closure {c : ℂ | ∃ m z, Mandelbrot.IsAttractingCycle (fun z ↦ z ^ 2 + c) m z} := by
  sorry

end LefebvreVariations
