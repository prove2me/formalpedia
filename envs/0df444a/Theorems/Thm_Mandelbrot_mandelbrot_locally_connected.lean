-- Prove2me | Theorems.Thm_Mandelbrot_mandelbrot_locally_connected
-- name    : Mandelbrot.mandelbrot_locally_connected
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T01:43:37.147534+00:00
-- url     : https://prove2.me/theorems/b9cbd859-ffd7-496e-97a7-1e5bf3f1b3c8
-- title:
--   MLC: the Mandelbrot set is locally connected
-- statement:
--   **Conjecture (MLC, Douady-Hubbard).** The Mandelbrot set
--
--   $$M = \{\, c \in \mathbb{C} : \text{the orbit of } 0 \text{ under } z \mapsto z^{2} + c \text{ is bounded} \,\}$$
--
--   is locally connected: every point of $M$, with the topology inherited from $\mathbb{C}$, has a neighbourhood basis consisting of connected sets.
--
--   Local connectivity of $M$ is one of the central open problems of one-dimensional complex dynamics. By work of Douady and Hubbard, MLC is equivalent to the statement that the inverse of the conformal isomorphism $\Phi : \mathbb{C} \setminus M \to \mathbb{C} \setminus \overline{\mathbb{D}}$ extends continuously to the unit circle, which would give a complete combinatorial model of $M$ (the *pinched disk* model); it implies the density of hyperbolicity in the quadratic family.
-- source:
--   https://en.wikipedia.org/wiki/Mandelbrot_set#Local_connectivity ; A. Douady and J. H. Hubbard, Etude dynamique des polynomes complexes, Orsay notes 1984/85

import Definitions.Def_mandelbrot_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- **The MLC conjecture**: the Mandelbrot set is locally connected. -/
theorem mandelbrot_locally_connected : LocallyConnectedSpace mandelbrotSet := by sorry

end Mandelbrot
