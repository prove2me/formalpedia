-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_point_dist_lt_half
-- name    : OAI.DoublingHilbert.point_dist_lt_half
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:47:58.821773+00:00
-- url     : https://prove2.me/theorems/43f08609-4e5d-4eb3-859b-e4d3e2ffa94a
-- title:
--   Matching coarse levels and $t/8$-close base points give distance less than $t/2$
-- statement:
--   Let $\ell^2=\ell^2(\mathbb{N})$ be the real Hilbert space of square-summable real sequences, with standard orthonormal basis $(e_n)_{n\ge 0}$. Let $s_j=1000^{-(j+1)}$ ($j\in\mathbb{N}$) be the scales of the construction and let $(j,i)\mapsto\langle j,i\rangle$ be a fixed pairing bijection of $\mathbb{N}\times\mathbb{N}$ onto $\mathbb{N}$. A base point $p=(p_1,p_2)\in\mathbb{R}^2$ and a finitely supported tuple $w:\mathbb{N}\to\mathbb{N}$ determine the point $\Phi(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\ne 0}s_j\,e_{2+\langle j,\,w_j-1\rangle}$ of $\ell^2$.
--
--   Let $t>0$, let $p,q\in\mathbb{R}^2$ and let $w,w'$ be arbitrary finitely supported tuples. Assume that the base points are $t/8$-close in each coordinate and that the tuples agree on every level whose scale exceeds $t/64$:
--
--   $$
--   |p_1-q_1|<\frac t8,\qquad |p_2-q_2|<\frac t8,\qquad w_j=w'_j\ \text{ for every } j \text{ with } s_j>\frac{t}{64}.
--   $$
--
--   Then
--
--   $$
--   \|\Phi(p,w)-\Phi(q,w')\|<\frac t2 .
--   $$
--
--   This is the diameter estimate behind the doubling bound of the constructed subset of Hilbert space: points of a ball of radius $t$ are sorted by the cell of width $t/8$ containing each base coordinate and by their tuple entries on the levels of scale larger than $t/64$, and the lemma shows that each such class has diameter less than $t/2$. Entries on the fine levels ($s_j\le t/64$) may differ arbitrarily.
--
--   **Formalization Note** In Lean, `p q : Base = ℝ × ℝ`, `w w' : Tuple = ℕ →₀ ℕ`, $s_j$ is `scale j`, $\Phi(p,w)$ is `point p w`, and the pairing is `Nat.pair`. No admissibility of $w,w'$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Doubling.lean#L171-L195

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Set
open Set Metric
open Set
open scoped BigOperators

theorem OAI.DoublingHilbert.point_dist_lt_half {p q : Base} {w w' : Tuple} {t : ℝ} (ht : 0 < t)
    (hx : |p.1 - q.1| < t / 8) (hy : |p.2 - q.2| < t / 8)
    (hlarge : ∀ j, t / 64 < scale j → w j = w' j) :
    dist (point p w) (point q w') < t / 2 := by sorry
