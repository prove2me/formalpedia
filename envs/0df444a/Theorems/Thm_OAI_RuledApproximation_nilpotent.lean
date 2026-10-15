-- Prove2me | Theorems.Thm_OAI_RuledApproximation_nilpotent
-- name    : OAI.RuledApproximation.nilpotent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:03:23.365549+00:00
-- url     : https://prove2.me/theorems/f1030e9d-9080-4976-8775-d167330ef1c2
-- title:
--   Nilpotent case: square-tile cylinder covers of ruled sets for fields whose derivative squares to zero
-- statement:
--   Let $Q=[-\tfrac12,\tfrac12]^2$ be the centred unit square of the Euclidean plane. A *square tile* is a set $T=\{c+a\,Rx : x\in Q\}$ with $c\in\mathbb{R}^2$, $R$ a linear isometry of the Euclidean plane and $a>0$, i.e. a congruent copy of a square of side $a$. For $T\subseteq\mathbb{R}^2$ and $g\in\mathbb{R}^2$ the *auxiliary cylinder* is the oblique prism $\operatorname{Aux}(T,g)=\{(s,\ b_1+s\,g_1,\ b_2+s\,g_2) : s\in\mathbb{R},\ b\in T\}\subseteq\mathbb{R}^3$. For $D\subseteq\mathbb{R}^2$ and $G=(G_1,G_2):\mathbb{R}^2\to\mathbb{R}^2$ let $\mathcal{R}_1(D,G,1)=\{(s,\ p_1+s\,G_1(p),\ p_2+s\,G_2(p)) : p\in D,\ |s|\le1\}$. For $h>0$ let $w_h(g)=1/\sqrt{1+g_1^2+h^2g_2^2}$, and define the *physical maps* $\Phi_h(z)=(z_1,z_2,hz_3)$ and $\Psi_{h,a}(z)=(z_2,z_1,h(a-z_3))$ of $\mathbb{R}^3$, for $a\in\mathbb{R}$.
--
--   A *cylinder* $C$ in $\mathbb{R}^3$ is given by a unit vector $u$ (its axis) and a base set $B\subseteq u^{\perp}$ in the plane orthogonal to $u$. Its carrier is the infinite cylinder $\operatorname{car}(C)=\{b+tu : b\in B,\ t\in\mathbb{R}\}$, and its area $\operatorname{area}(C)$ is the two-dimensional Lebesgue measure of $B$ inside the plane $u^{\perp}$. It is a *parallelogram cylinder* if $B=\{c+sx+ty : s,t\in[0,1]\}$ for some $c,x,y\in u^{\perp}$ with $x,y$ linearly independent.
--
--   **Theorem.** Let $D\subseteq\mathbb{R}^2$ be compact, let $G:\mathbb{R}^2\to\mathbb{R}^2$ be $C^\infty$ on an open set containing $D$, and suppose $DG(b)\circ DG(b)=0$ for every $b\in D$. Then for all $h>0$ and $\varepsilon>0$ there are $n\in\mathbb{N}$, square tiles $T_1,\dots,T_n$ and vectors $g_1,\dots,g_n\in\mathbb{R}^2$ such that:
--   1. the auxiliary cylinders cover the ruled set, $\mathcal{R}_1(D,G,1)\subseteq\bigcup_{i=1}^n\operatorname{Aux}(T_i,g_i)$;
--   2. their weighted area is controlled by the integral of the weight,
--   $$\sum_{i=1}^n|T_i|\,w_h(g_i)\le\int_D w_h(G(b))\,db+\varepsilon ,$$
--   where $|T_i|$ is the Lebesgue measure of $T_i$;
--   3. for every $a\in\mathbb{R}$ there are parallelogram cylinders $C^{(1)}_1,\dots,C^{(1)}_n$ and $C^{(2)}_1,\dots,C^{(2)}_n$ such that, for each $i$,
--   $$\operatorname{car}\bigl(C^{(1)}_i\bigr)=\Phi_h\bigl(\operatorname{Aux}(T_i,g_i)\bigr),\quad \operatorname{car}\bigl(C^{(2)}_i\bigr)=\Psi_{h,a}\bigl(\operatorname{Aux}(T_i,g_i)\bigr),\quad \operatorname{area}\bigl(C^{(1)}_i\bigr)=\operatorname{area}\bigl(C^{(2)}_i\bigr)=h\,|T_i|\,w_h(g_i).$$
--
--   This is the nilpotent case of the main covering theorem for ruled sets. The tiles and directions form a single certificate in normalized coordinates; item 3 realizes every auxiliary prism as a genuine Euclidean cylinder perpendicular to its lines in two physical placements: through $\Phi_h$, which stretches the third coordinate by $h$, and through $\Psi_{h,a}$, which also swaps the first two coordinates and replaces the height $z_3$ by $a-z_3$ before stretching. In each placement the total area of the cylinders is $h$ times the weighted sum in item 2.
--
--   **Formalization Note** The statement is the proposition `NilpotentStatement`. "$C^\infty$ on an open set containing $D$" is `SmoothNear ∞ D G` (smooth, not analytic); the auxiliary cylinder is `auxiliaryCylinder T g`, the maps are `firstPhysicalMap h` and `secondPhysicalMap h a`, the ruled set is `physicalRuled 1 D G 1`, and $|T_i|$ is `volume.real (T i)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Nilpotent.lean#L55-L98

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
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.nilpotent : NilpotentStatement := by sorry
