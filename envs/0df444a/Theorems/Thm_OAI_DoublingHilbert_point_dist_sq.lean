-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_point_dist_sq
-- name    : OAI.DoublingHilbert.point_dist_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:19:38.605108+00:00
-- url     : https://prove2.me/theorems/00d8e6aa-a4ce-4f84-8e03-3922109c73c9
-- title:
--   Pythagorean decomposition of distances between points of the strip set
-- statement:
--   Work in real $\ell^2$ with standard unit vectors $e_0,e_1,e_2,\dots$. The strip construction attaches to a base point $p=(p_1,p_2)\in\mathbb{R}^2$ and a finitely supported tuple $w:\mathbb{N}\to\mathbb{N}$ the point
--   $$
--   z(p,w)=p_1e_0+p_2e_1+\sum_{j\in\mathbb{N}}\epsilon_j(w),
--   $$
--   where the level-$j$ component is $\epsilon_j(w)=0$ if $w_j=0$ and $\epsilon_j(w)=r_j\,e_{2+\pi(j,w_j-1)}$ if $w_j\neq0$. Here $r_j=1000^{-(j+1)}$ and $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ is a pairing bijection, so different pairs (level, color) use different coordinates, none equal to $0$ or $1$.
--
--   **Theorem.** Let $p,q\in\mathbb{R}^2$, let $w,w'$ be finitely supported tuples, and let $s\subseteq\mathbb{N}$ be a finite set containing the supports of both $w$ and $w'$. Then
--   $$
--   \|z(p,w)-z(q,w')\|^2=(p_1-q_1)^2+(p_2-q_2)^2+\sum_{j\in s}\bigl\|\epsilon_j(w)-\epsilon_j(w')\bigr\|^2 .
--   $$
--   No admissibility of $(p,w)$ or $(q,w')$ is assumed.
--
--   Each summand is $0$ if $w_j=w'_j$, $r_j^2$ if exactly one of $w_j,w'_j$ vanishes, and $2r_j^2$ if both are nonzero and different. This exact decomposition drives the doubling estimate for the strip set: coordinates at coarse levels are frozen inside small balls, two different choices at one level are at least $r_j$ apart, and the fine levels contribute a geometrically small tail.
--
--   **Formalization Note** The points are `point p w`, the components are `entryVector w j`, and the distance is the norm distance of `RealL2`; $p_1,p_2$ are `p.1`, `p.2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Construction.lean#L260-L280

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction

open OAI OAI.DoublingHilbert
open scoped BigOperators
open Set

theorem OAI.DoublingHilbert.point_dist_sq (p q : Base) (w w' : Tuple) (s : Finset ℕ)
    (hw : w.support ⊆ s) (hw' : w'.support ⊆ s) :
    dist (point p w) (point q w') ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 +
      ∑ j ∈ s, ‖entryVector w j - entryVector w' j‖ ^ 2 := by sorry
