-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_Segment_integral_grid
-- name    : OAI.DoublingHilbert.Segment.integral_grid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:26:27.866787+00:00
-- url     : https://prove2.me/theorems/ab8339c4-2a3b-432b-8e93-83519959d96b
-- title:
--   The mean over $n$ adjacent equal cells is the average of the cell means
-- statement:
--   Let $E$ be a real normed space, let $a\in\mathbb{R}$, $h>0$ and let $n\ge1$ be an integer. Let $g:\mathbb{R}\to E$ be bounded and strongly measurable. Divide the interval $[a,a+nh]$ into the $n$ adjacent cells $[a+ih,\,a+(i+1)h]$, $i=0,1,\dots,n-1$. Then the mean of $g$ over the whole interval is the arithmetic mean of its means over the cells:
--
--   $$
--   \frac{1}{nh}\int_a^{a+nh}g(x)\,dx=\frac1n\sum_{i=0}^{n-1}\frac1h\int_{a+ih}^{a+(i+1)h}g(x)\,dx .
--   $$
--
--   This exact finite averaging identity is the one-dimensional basis for writing the mean over a rectangle as the average of the means over its columns or rows of cells. Combined with the fact that some term of a finite average is at most the average, it produces a cell or block whose mean is no larger than the mean over the whole grid.
--
--   **Formalization Note** The means are integrals against the uniform laws `(grid a h n hh hn).law` and `(cell a h hh i).law` (normalized Lebesgue measure on the half-open intervals $(a,a+nh]$ and $(a+ih,a+(i+1)h]$), and the sum runs over `Fin n`. Integrals are Bochner integrals; completeness of $E$ is not assumed, and for a non-complete $E$ Mathlib's Bochner integral is $0$, so the identity is then trivial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Rectangles.lean#L433-L449

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles

open OAI OAI.DoublingHilbert OAI.DoublingHilbert.Segment
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology

theorem OAI.DoublingHilbert.Segment.integral_grid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n) {g : ℝ → E}
    (hg : IsBoundedField g) :
    (∫ x, g x ∂(grid a h n hh hn).law) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, ∫ x, g x ∂(cell a h hh i).law := by sorry
