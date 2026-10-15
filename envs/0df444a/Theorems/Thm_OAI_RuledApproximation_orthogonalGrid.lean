-- Prove2me | Theorems.Thm_OAI_RuledApproximation_orthogonalGrid
-- name    : OAI.RuledApproximation.orthogonalGrid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:54:19.5463+00:00
-- url     : https://prove2.me/theorems/20bb9cb8-538f-4856-b55c-3f9e82d38d14
-- title:
--   Orthogonal-grid case: parallelogram-cylinder covers of the $\sqrt{2}$-scaled ruled set for trace-free saddle fields with $\|Dv\|\le\kappa<1$
-- statement:
--   A *cylinder* $C$ in $\mathbb{R}^3$ is given by a unit vector $u$ (its axis) and a base set $B\subseteq u^{\perp}$ in the plane orthogonal to $u$. Its carrier is the infinite cylinder $\operatorname{car}(C)=\{b+tu : b\in B,\ t\in\mathbb{R}\}$, and its area $\operatorname{area}(C)$ is the two-dimensional Lebesgue measure of $B$ inside the plane $u^{\perp}$. It is a *parallelogram cylinder* if $B=\{c+sx+ty : s,t\in[0,1]\}$ for some $c,x,y\in u^{\perp}$ with $x,y$ linearly independent.
--
--   For $h>0$, a set $D\subseteq\mathbb{R}^2$, a map $v=(v_1,v_2):\mathbb{R}^2\to\mathbb{R}^2$ and $L\ge 0$, the *ruled set* $\mathcal{R}_h(D,v,L)=\{(s,\ p_1+s\,v_1(p),\ h\,(p_2+s\,v_2(p))) : p\in D,\ |s|\le L\}\subseteq\mathbb{R}^3$ is the union, over $p\in D$, of the segments through $(0,p_1,hp_2)$ in direction $(1,v_1(p),h\,v_2(p))$ whose first coordinate ranges over $[-L,L]$. The associated *weight* is $w_h(g)=1/\sqrt{1+g_1^2+h^2g_2^2}$ for $g\in\mathbb{R}^2$; it is the reciprocal length of the direction vector $(1,g_1,hg_2)$.
--
--   **Theorem.** Let $D\subseteq\mathbb{R}^2$ be compact with Lebesgue-null topological boundary, let $v:\mathbb{R}^2\to\mathbb{R}^2$ be $C^1$ on some open set containing $D$, and let $\kappa<1$. Suppose that at every $p\in D$ the derivative $Dv(p)$ satisfies
--   $$\operatorname{tr}Dv(p)=0,\qquad \det Dv(p)<0,\qquad \|Dv(p)\|\le\kappa,$$
--   where $\|\cdot\|$ is the operator norm with respect to the Euclidean norm. Then for every $\varepsilon>0$ the ruled set $\mathcal{R}_{\sqrt2}(D,v,1)$ is covered by finitely many parallelogram cylinders of total area at most
--   $$\sqrt{2}\int_D\frac{dp}{\sqrt{1+v_1(p)^2+2\,v_2(p)^2}}+\varepsilon .$$
--
--   This is the orthogonal-grid case of the main covering theorem for ruled sets. The integrand is the weight $w_{\sqrt2}(v(p))$, the reciprocal length of the direction $(1,v_1(p),\sqrt2\,v_2(p))$ of the segment through $(0,p_1,\sqrt2\,p_2)$. A bundle of parallel lines in this direction through the embedded copy of a small footprint of area $\alpha$ around $p$ has perpendicular cross-section $\sqrt2\,\alpha\,w_{\sqrt2}(v(p))$, so the bound is the total perpendicular cross-section of the ruling, up to $\varepsilon$.
--
--   **Formalization Note** The statement is the proposition `OrthogonalGridStatement`. "$C^1$ on an open set containing $D$" is `SmoothNear 1 D v`; trace and determinant are those of `(fderiv ℝ v p).toLinearMap`, and the norm is the operator norm of `fderiv ℝ v p` on `EuclideanSpace ℝ (Fin 2)`. The coordinates $v_1,v_2$ are `v p 0`, `v p 1`, and the integral is over Lebesgue measure on the plane.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SpecializedCover.lean#L105-L119

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

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.orthogonalGrid : OrthogonalGridStatement := by sorry
