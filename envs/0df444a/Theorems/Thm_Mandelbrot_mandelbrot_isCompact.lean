-- Prove2me | Theorems.Thm_Mandelbrot_mandelbrot_isCompact
-- name    : Mandelbrot.mandelbrot_isCompact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:01:47.477142+00:00
-- url     : https://prove2.me/theorems/3a1a0d03-9b52-48fc-8804-caac41391459
-- title:
--   The Mandelbrot set is compact
-- statement:
--   **Theorem.** The Mandelbrot set $M$ is a compact subset of $\mathbb{C}$.
--
--   Boundedness follows from the escape criterion, $M$ being contained in the closed disk of radius $2$, and closedness holds because $M$ is the intersection over $k$ of the closed sets $\{c : |f_c^{\,k}(0)| \le 2\}$, each closed by continuity of the polynomial $c \mapsto f_c^{\,k}(0)$. Compactness is what makes questions about the area and the Hausdorff dimension of $\partial M$ meaningful.
-- source:
--   https://en.wikipedia.org/wiki/Mandelbrot_set#Basic_properties

import Definitions.Def_mandelbrot_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- The Mandelbrot set is compact. -/
theorem mandelbrot_isCompact : IsCompact mandelbrotSet := by sorry

end Mandelbrot
