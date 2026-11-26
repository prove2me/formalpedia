-- Prove2me | Theorems.Thm_LefebvreVariations_mandelbrot_cardioid_subset
-- name    : LefebvreVariations.mandelbrot_cardioid_subset
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:10:51.8377+00:00
-- url     : https://prove2.me/theorems/6c201a2b-f294-5015-a4e7-e7ead0aea644
-- title:
--   Lefebvre's variations, No. 51 — on a theme by Douady and Hubbard: the main cardioid is contained in the Mandelbrot set
-- statement:
--   Every parameter $c=\mu/2-\mu^2/4$ with $|\mu|<1$ lies in the Mandelbrot set:
--   $$
--   \Bigl\{\tfrac{\mu}{2}-\tfrac{\mu^{2}}{4} \;:\; \mu\in\mathbb{C},\ |\mu|<1\Bigr\} \;\subseteq\; M,
--   $$
--   where $M=\{c\in\mathbb{C} : \text{the orbit of }0\text{ under }z\mapsto z^2+c\text{ does not tend to }\infty\}$.
--
--   For such $c$ the point $z=\mu/2$ is a fixed point of $z\mapsto z^2+c$ with multiplier $\mu$, hence attracting, and the critical point $0$ is attracted to it; the set is the open main cardioid of $M$. It is a piece of the structure of the set whose local connectivity (MLC) is open.
--
--   **Formalization Note** The set on the left is `{c : ℂ | ∃ μ : ℂ, ‖μ‖ < 1 ∧ c = μ / 2 - μ ^ 2 / 4}` and the right side is `Mandelbrot.mandelbrotSet`, the platform's set of parameters for which the orbit of $0$ under $z\mapsto z^2+c$ does not tend to infinity in the cobounded filter. Only the inclusion is asserted.
--
--   **Why this is a variation.** Variation on the open mission 'Local Connectivity of the Mandelbrot Set (MLC)'. It is a key lemma about the structure of the set, namely that the main hyperbolic component is inside it, stated with the parent's own mandelbrotSet; the hyperbolic components are the part of the interior where MLC is known, and this inclusion is the first one.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. Douady and J. H. Hubbard, Etude dynamique des polynomes complexes I, Publ. Math. Orsay 84-02 (1984) (the main cardioid as the hyperbolic component of period 1); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Princeton 2006 (cited from memory, no section number). The inclusion follows from the standard fact that a critical point attracted to a finite attracting cycle has bounded orbit; the parametrisation c = mu/2 - mu^2/4 of the cardioid by the multiplier mu is an elementary computation (z = mu/2 is fixed with multiplier 2z = mu). Origin: the open mission on the local connectivity of the Mandelbrot set (MLC).

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric

namespace LefebvreVariations

/-- The main cardioid `{μ/2 - μ²/4 : |μ| < 1}` lies in the Mandelbrot set. -/
theorem mandelbrot_cardioid_subset :
    {c : ℂ | ∃ μ : ℂ, ‖μ‖ < 1 ∧ c = μ / 2 - μ ^ 2 / 4} ⊆ Mandelbrot.mandelbrotSet := by
  sorry

end LefebvreVariations
