-- Prove2me | Theorems.Thm_OAI_RuledApproximation_framed_local_cover_of_shape
-- name    : OAI.RuledApproximation.framed_local_cover_of_shape
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:00:22.361563+00:00
-- url     : https://prove2.me/theorems/0b0f840a-db42-4722-b90f-a46b38aa79cf
-- title:
--   From weighted lattice certificates to finite covers by projected cylinders in a linear frame
-- statement:
--   A *cylinder* $C$ in $\mathbb{R}^3$ is given by a unit vector $u$ (its axis) and a base set $B\subseteq u^{\perp}$ in the plane orthogonal to $u$. Its carrier is the infinite cylinder $\operatorname{car}(C)=\{b+tu : b\in B,\ t\in\mathbb{R}\}$, and its area $\operatorname{area}(C)$ is the two-dimensional Lebesgue measure of $B$ inside the plane $u^{\perp}$. It is a *parallelogram cylinder* if $B=\{c+sx+ty : s,t\in[0,1]\}$ for some $c,x,y\in u^{\perp}$ with $x,y$ linearly independent. For a class $\mathcal{S}$ of cylinders, a set $Z\subseteq\mathbb{R}^3$ has a *finite $\mathcal{S}$-cover of total area at most $A$* if there are finitely many cylinders $C_1,\dots,C_n\in\mathcal{S}$ ($n\ge 0$) with $Z\subseteq\bigcup_i\operatorname{car}(C_i)$ and $\sum_i\operatorname{area}(C_i)\le A$.
--
--   For $h>0$, a set $D\subseteq\mathbb{R}^2$, a map $v=(v_1,v_2):\mathbb{R}^2\to\mathbb{R}^2$ and $L\ge 0$, the *ruled set* $\mathcal{R}_h(D,v,L)=\{(s,\ p_1+s\,v_1(p),\ h\,(p_2+s\,v_2(p))) : p\in D,\ |s|\le L\}\subseteq\mathbb{R}^3$ is the union, over $p\in D$, of the segments through $(0,p_1,hp_2)$ in direction $(1,v_1(p),h\,v_2(p))$ whose first coordinate ranges over $[-L,L]$. The associated *weight* is $w_h(g)=1/\sqrt{1+g_1^2+h^2g_2^2}$ for $g\in\mathbb{R}^2$; it is the reciprocal length of the direction vector $(1,g_1,hg_2)$. For $h>0$, $g\in\mathbb{R}^2$ and $P\subseteq\mathbb{R}^2$, the *projected cylinder* $\mathcal{C}_{h,g}(P)$ is the cylinder whose axis is the unit vector in the direction $(1,g_1,hg_2)$ and whose base is the orthogonal projection, onto the plane perpendicular to that axis, of the planar set $\{(0,p_1,hp_2) : p\in P\}$. Its carrier is $\{(s,\ p_1+s\,g_1,\ h\,(p_2+s\,g_2)) : p\in P,\ s\in\mathbb{R}\}$, the union of the full lines in direction $(1,g_1,hg_2)$ through the points of the embedded copy of $P$.
--
--   On the coordinate side, $\mathbb{R}^2$ carries the maximum norm $\|x\|_\infty$, with closed balls $\bar B_\infty(b,a)=[b_1-a,b_1+a]\times[b_2-a,b_2+a]$, and a *frame* is a linear isomorphism $M$ from this coordinate plane onto the Euclidean plane. A linear map $A$ of the coordinate plane satisfies the *lattice model with time bound $L$ and radius $R$* if for every integer $n\ge1$, every $p$ and every $|r|\le L$ there is $b\in\tfrac1n\mathbb{Z}^2$ with $\|b-p\|_\infty\le R/n$ and $\|(p-b)+r\,A(p-b)\|_\infty\le\tfrac1{2n}$.
--
--   **Theorem.** Let $M$ be a frame and let $h>0$, $L\ge0$, $R\ge0$, $\delta\ge0$. Let $\mathcal{S}$ be any class of cylinders containing every projected cylinder $\mathcal{C}_{h,g}\bigl(M(\bar B_\infty(b,a))\bigr)$ with $b,g\in\mathbb{R}^2$ and $a>0$. Let $K\subseteq U$ be subsets of the coordinate plane with $K$ compact and $U$ open, let $v:\mathbb{R}^2\to\mathbb{R}^2$ be a map, and let $A$ be a linear map satisfying the lattice model with time bound $L$ and radius $R$, such that the field in coordinates is $\delta$-close to its linear model on $U$:
--   $$\bigl\|M^{-1}v(Mp)-M^{-1}v(Mb)-A(p-b)\bigr\|_\infty\le\delta\,\|p-b\|_\infty\qquad\text{for all }p,b\in U .$$
--   Let $F$ be a continuous nonnegative function on the coordinate plane with $F(p)=w_h(v(Mp))$ for $p\in U$. Then for every $\varepsilon>0$ the ruled set $\mathcal{R}_h(M(K),v,L)$ has a finite $\mathcal{S}$-cover of total area at most
--   $$h\,(1+2L\delta R)^2\int_{M(K)}w_h(v(q))\,dq+\varepsilon .$$
--
--   This is the step that turns the combinatorial covering certificate (finitely many lattice labels with a controlled weighted count) into actual Euclidean cylinders perpendicular to the ruling directions. The factor $(1+2L\delta R)^2$ is the area inflation caused by the linearization error $\delta$ and tends to $1$ as $\delta\to0$. The shape class $\mathcal{S}$ is a parameter so that the same construction produces parallelogram cylinders in the hyperbolic case and square-tile cylinders in the nilpotent case.
--
--   **Formalization Note** The frame is `M : Coordinates ≃L[ℝ] Plane` with `Coordinates = Fin 2 → ℝ` (sup norm) and `Plane = EuclideanSpace ℝ (Fin 2)`; the lattice model is `LatticeModel A L R`, the projected cylinder is `projectedCylinder h g P`, the shape class is a predicate `shape : Cylinder → Prop`, and the integral is over Lebesgue measure on the Euclidean plane.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SquareCover.lean#L12-L83

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

theorem OAI.RuledApproximation.framed_local_cover_of_shape (M : Coordinates ≃L[ℝ] Plane) {h L R delta : ℝ}
    (shape : Cylinder → Prop)
    (hshape : ∀ b : Coordinates, ∀ a : ℝ, 0 < a → ∀ g : Plane,
      shape (projectedCylinder h g (M '' closedBall b a)))
    (hh : 0 < h) (hL : 0 ≤ L) (hR : 0 ≤ R) (hd : 0 ≤ delta)
    {K U : Set Coordinates} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (v : Plane → Plane) (A : Coordinates →L[ℝ] Coordinates)
    (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖M.symm (v (M p)) - M.symm (v (M b)) - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Coordinates → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    (hFval : ∀ p ∈ U, F p = physicalWeight h (v (M p)))
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h (M '' K) v L)
      (h * (1 + 2 * L * delta * R) ^ 2 *
        (∫ p in M '' K, physicalWeight h (v p)) + eps) := by sorry
