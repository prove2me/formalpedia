-- Prove2me | Theorems.Thm_Mandelbrot_mandelbrot_isConnected
-- name    : Mandelbrot.mandelbrot_isConnected
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:03:23.211789+00:00
-- url     : https://prove2.me/theorems/8f003cdb-c5f8-4a54-8afc-a25c34dc600f
-- title:
--   Douady-Hubbard: the Mandelbrot set is connected
-- statement:
--   **Theorem (Douady-Hubbard, 1982).** The Mandelbrot set is connected.
--
--   Douady and Hubbard proved this by constructing an explicit conformal isomorphism
--
--   $$\Phi : \mathbb{C} \setminus M \longrightarrow \mathbb{C} \setminus \overline{\mathbb{D}},$$
--
--   given by the Boettcher coordinate of the escaping critical value, which shows that the complement of $M$ in the Riemann sphere is conformally a disk; hence $M$ is connected and full. MLC asks for the much finer statement that the inverse of $\Phi$ extends continuously to the unit circle. The formal statement also records that $M$ is nonempty, which is part of the notion of a connected set used here.
-- source:
--   A. Douady and J. H. Hubbard, Iteration des polynomes quadratiques complexes, C. R. Acad. Sci. Paris Ser. I Math. 294 (1982), 123-126 ; https://en.wikipedia.org/wiki/Mandelbrot_set#Basic_properties

import Definitions.Def_mandelbrot_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- **Douady-Hubbard (1982)**: the Mandelbrot set is connected (and nonempty). -/
theorem mandelbrot_isConnected : IsConnected mandelbrotSet := by sorry

end Mandelbrot
