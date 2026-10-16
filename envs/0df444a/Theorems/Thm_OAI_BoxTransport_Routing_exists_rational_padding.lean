-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_exists_rational_padding
-- name    : OAI.BoxTransport.Routing.exists_rational_padding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:11:50.806559+00:00
-- url     : https://prove2.me/theorems/0daa95a2-1524-4fa3-a15b-461b8f1deebb
-- title:
--   A common small rational padding keeps finitely many disjoint boxes disjoint
-- statement:
--   Let $n\in\mathbb{N}$ and, for $i\in\{1,\dots,n\}$, let $a_i,b_i,h_i,k_i\in\mathbb{Q}^3$ with $h_{il}\ge0$ and $k_{il}\ge0$ for every $i$ and every coordinate $l\in\{1,2,3\}$. For $c,r\in\mathbb{R}^3$ let $B(c,r)=\{x\in\mathbb{R}^3: |x_l-c_l|\le r_l,\ l=1,2,3\}$ be the closed box with center $c$ and half-widths $r$, and write $\mathbf 1=(1,1,1)$. Assume that the source boxes $B(a_i,h_i)$ are pairwise disjoint and that the target boxes $B(b_i,k_i)$ are pairwise disjoint (for $i\ne j$).
--
--   **Theorem.** For every rational $R>0$ there is a rational $\eta$ with $0<\eta<R/8$ such that for all $i\neq j$
--
--   $$B(a_i,\,h_i+2\eta\mathbf 1)\cap B(a_j,\,h_j+2\eta\mathbf 1)=\varnothing\qquad\text{and}\qquad B(b_i,\,k_i+2\eta\mathbf 1)\cap B(b_j,\,k_j+2\eta\mathbf 1)=\varnothing .$$
--
--   A finite family of pairwise disjoint closed boxes can thus be enlarged by one common rational margin $2\eta$ on every side without creating intersections, and the margin can be taken below any prescribed rational bound; the same margin works simultaneously for the source and the target family. In the box-routing construction this margin is the room in which smooth cutoff functions interpolate between the motions of different boxes, and its rationality keeps the construction inside exact rational arithmetic.
--
--   **Formalization Note** The source boxes are `solidBox (a i) (h i)`, i.e. `realBox` of the real casts of the rational data, and the padded boxes are `realBox (realPoint (a i)) (fun l => h i l + 2 * η)`. Pairwise disjointness is expressed with Mathlib's `Pairwise`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Geometry.lean#L260-L300

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry

open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.exists_rational_padding {n : ℕ} (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 ≤ h i j) (hk : ∀ i j, 0 ≤ k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (R : ℚ) (hR : 0 < R) :
    ∃ η : ℚ, 0 < η ∧ η < R / 8 ∧
      (Pairwise fun i j =>
        Disjoint (realBox (realPoint (a i)) (fun l => (h i l : ℝ) + 2 * η))
          (realBox (realPoint (a j)) (fun l => (h j l : ℝ) + 2 * η))) ∧
      (Pairwise fun i j =>
        Disjoint (realBox (realPoint (b i)) (fun l => (k i l : ℝ) + 2 * η))
          (realBox (realPoint (b j)) (fun l => (k j l : ℝ) + 2 * η))) := by sorry
