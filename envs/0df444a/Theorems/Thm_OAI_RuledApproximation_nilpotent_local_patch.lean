-- Prove2me | Theorems.Thm_OAI_RuledApproximation_nilpotent_local_patch
-- name    : OAI.RuledApproximation.nilpotent_local_patch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:00:48.263951+00:00
-- url     : https://prove2.me/theorems/8c148bf4-20e5-405d-862b-8c5bbdece074
-- title:
--   Local square-tile cylinder covers near a point where the derivative squares to zero
-- statement:
--   A *cylinder* $C$ in $\mathbb{R}^3$ is given by a unit vector $u$ (its axis) and a base set $B\subseteq u^{\perp}$ in the plane orthogonal to $u$. Its carrier is the infinite cylinder $\operatorname{car}(C)=\{b+tu : b\in B,\ t\in\mathbb{R}\}$, and its area $\operatorname{area}(C)$ is the two-dimensional Lebesgue measure of $B$ inside the plane $u^{\perp}$. It is a *parallelogram cylinder* if $B=\{c+sx+ty : s,t\in[0,1]\}$ for some $c,x,y\in u^{\perp}$ with $x,y$ linearly independent.
--
--   For $h>0$, a set $D\subseteq\mathbb{R}^2$, a map $v=(v_1,v_2):\mathbb{R}^2\to\mathbb{R}^2$ and $L\ge 0$, the *ruled set* $\mathcal{R}_h(D,v,L)=\{(s,\ p_1+s\,v_1(p),\ h\,(p_2+s\,v_2(p))) : p\in D,\ |s|\le L\}\subseteq\mathbb{R}^3$ is the union, over $p\in D$, of the segments through $(0,p_1,hp_2)$ in direction $(1,v_1(p),h\,v_2(p))$ whose first coordinate ranges over $[-L,L]$. The associated *weight* is $w_h(g)=1/\sqrt{1+g_1^2+h^2g_2^2}$ for $g\in\mathbb{R}^2$; it is the reciprocal length of the direction vector $(1,g_1,hg_2)$. For $h>0$, $g\in\mathbb{R}^2$ and $P\subseteq\mathbb{R}^2$, the *projected cylinder* $\mathcal{C}_{h,g}(P)$ is the cylinder whose axis is the unit vector in the direction $(1,g_1,hg_2)$ and whose base is the orthogonal projection, onto the plane perpendicular to that axis, of the planar set $\{(0,p_1,hp_2) : p\in P\}$. Its carrier is $\{(s,\ p_1+s\,g_1,\ h\,(p_2+s\,g_2)) : p\in P,\ s\in\mathbb{R}\}$, the union of the full lines in direction $(1,g_1,hg_2)$ through the points of the embedded copy of $P$.
--
--   Let $Q=[-\tfrac12,\tfrac12]^2$ be the centred unit square of the Euclidean plane. A *square tile* is a set $T=\{c+a\,Rx : x\in Q\}$ with $c\in\mathbb{R}^2$, $R$ a linear isometry of the Euclidean plane and $a>0$, i.e. a congruent copy of a square of side $a$. A *square-tile cylinder* is a projected cylinder $\mathcal{C}_{h,g}(T)$ with $g\in\mathbb{R}^2$ arbitrary and $T$ a square tile.
--
--   **Theorem.** Let $h>0$ and $B>1$, let $U\subseteq\mathbb{R}^2$ be open, let $v:\mathbb{R}^2\to\mathbb{R}^2$ be $C^1$ on $U$, and let $p\in U$ be a point with $Dv(p)\circ Dv(p)=0$. Then there is an open set $V$ containing $p$ such that for every compact $K\subseteq V$ and every $\varepsilon>0$ the ruled set $\mathcal{R}_h(K,v,1)$ is covered by finitely many square-tile cylinders of total area at most
--   $$h\,B\int_K w_h(v(q))\,dq+\varepsilon .$$
--
--   The neighbourhood $V$ depends on $B$ but not on $K$ or $\varepsilon$. Since $B>1$ is arbitrary, near a point with nilpotent derivative the ruled set can be covered at a cost arbitrarily close to $h\int_K w_h(v)$, with no smallness condition on $Dv(p)$. This is the local building block of the nilpotent case of the main covering theorem; compactness then globalizes it.
--
--   **Formalization Note** The cylinder class is `squareProjected h`, i.e. `∃ T g, IsSquareTile T ∧ C = projectedCylinder h g T`; the ruled set is `physicalRuled h K v 1`, the hypothesis on the derivative is `(fderiv ℝ v p).comp (fderiv ℝ v p) = 0`, and the integral is over Lebesgue measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SquareCover.lean#L86-L155

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.nilpotent_local_patch {h B : ℝ} (hh : 0 < h) (hB : 1 < B)
    {v : Plane → Plane} {U : Set Plane} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : Plane} (hp : p ∈ U) (hnil : (fderiv ℝ v p).comp (fderiv ℝ v p) = 0) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ ∀ K : Set Plane, IsCompact K → K ⊆ V →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover (squareProjected h) (physicalRuled h K v 1)
        (h * B * (∫ q in K, physicalWeight h (v q)) + eps) := by sorry
