-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_Rectangle_integral_le_four_of_subset
-- name    : OAI.DoublingHilbert.Rectangle.integral_le_four_of_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:24:02.979126+00:00
-- url     : https://prove2.me/theorems/66d04cdd-f233-4acc-91c7-9502ebf3e1d3
-- title:
--   Mean of a nonnegative function on a subrectangle keeping half of each side is at most four times the full mean
-- statement:
--   Let $P=[a_0,a_1]\times[b_0,b_1]$ and $Q=[c_0,c_1]\times[d_0,d_1]$ be closed rectangles in $\mathbb{R}^2$ with $a_0<a_1$, $b_0<b_1$, $c_0<c_1$, $d_0<d_1$, such that $Q\subseteq P$ and each side of $Q$ is at least half the corresponding side of $P$:
--   $$c_1-c_0\ge\tfrac12\,(a_1-a_0),\qquad d_1-d_0\ge\tfrac12\,(b_1-b_0).$$
--   Let $g:\mathbb{R}^2\to\mathbb{R}$ be a bounded measurable function with $g(p)\ge0$ for every $p$. For a rectangle $T$ of area $|T|$ write $\mathbb{E}_T[g]=\frac{1}{|T|}\int_Tg$ for the mean of $g$ over $T$. Then
--
--   $$
--   \mathbb{E}_Q[g]\le4\,\mathbb{E}_P[g].
--   $$
--
--   Trimming a rectangle to a subrectangle that keeps at least half of each side thus increases the mean of a nonnegative quantity by at most a factor four. In the construction of a doubling subset of $\ell^2$ without bi-Lipschitz embeddings into $\mathbb{R}^k$, this transfers small mean-square derivative errors from a small square around a Lebesgue point to an inscribed grid of complete period blocks.
--
--   **Formalization Note** The means are integrals against `Rectangle.law`, the uniform probability measure on the rectangle (normalized Lebesgue measure on the half-open box, which gives the same means as the closed box). Boundedness and measurability are the hypothesis `IsBoundedField g` (strongly measurable and uniformly bounded), and the inclusion is `Q.closed ⊆ P.closed` between the closed boxes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Rectangles.lean#L347-L364

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles

open OAI OAI.DoublingHilbert OAI.DoublingHilbert.Rectangle
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology

theorem OAI.DoublingHilbert.Rectangle.integral_le_four_of_subset (P Q : Rectangle) {g : Base → ℝ}
    (hg : IsBoundedField g) (hpos : ∀ p, 0 ≤ g p)
    (hsub : Q.closed ⊆ P.closed)
    (hx : P.x.length / 2 ≤ Q.x.length) (hy : P.y.length / 2 ≤ Q.y.length) :
    (∫ p, g p ∂Q.law) ≤ 4 * (∫ p, g p ∂P.law) := by sorry
