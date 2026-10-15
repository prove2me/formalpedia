-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_Segment_exists_grid_inside
-- name    : OAI.DoublingHilbert.Segment.exists_grid_inside
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:27:22.432707+00:00
-- url     : https://prove2.me/theorems/a2f1892f-07a1-4187-a962-ff81b31bb941
-- title:
--   Inscribing whole $h$-lattice cells that cover at least half of an interval of length greater than $4h$
-- statement:
--   Let $I=[\alpha,\beta]$ be an interval with $\alpha<\beta$ and length $|I|=\beta-\alpha$, and let $h$ be a real number with
--   $$0<h<\tfrac14\,|I| .$$
--   Then there exist an integer $a$ and an integer $n\ge1$ such that the interval $[ah,(a+n)h]$, a union of $n$ consecutive cells of the lattice $h\mathbb{Z}$, lies in $I$ and has at least half its length:
--
--   $$
--   \alpha\le ah,\qquad (a+n)h\le\beta,\qquad nh\ge\tfrac12\,|I| .
--   $$
--
--   An interval can therefore be trimmed to a whole number of lattice periods, aligned with the global lattice $h\mathbb{Z}$, while losing at most two periods. Applied to both sides of a rectangle with the horizontal and vertical periods of a level of the strip pattern, it produces an inscribed grid of complete period blocks that keeps at least half of each side.
--
--   **Formalization Note** The interval is `Segment.grid (a * h) h n hh hn`, with left endpoint $ah$, right endpoint $ah+nh$ and length $nh$; the existential also packages the proof of $0<n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Grids.lean#L92-L127

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids

open OAI OAI.DoublingHilbert OAI.DoublingHilbert.Segment
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology

theorem OAI.DoublingHilbert.Segment.exists_grid_inside (I : Segment) {h : ℝ} (hh : 0 < h)
    (hsmall : h < I.length / 4) :
    ∃ (a : ℤ) (n : ℕ) (hn : 0 < n),
      I.lo ≤ (grid (a * h) h n hh hn).lo ∧
      (grid (a * h) h n hh hn).hi ≤ I.hi ∧
      I.length / 2 ≤ (grid (a * h) h n hh hn).length := by sorry
