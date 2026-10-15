-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singular
-- name    : OAI.RuledApproximation.singular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:24:06.905361+00:00
-- url     : https://prove2.me/theorems/60e88ff4-0643-461b-bdef-88d9f70350f9
-- title:
--   Finite cylinder covers of the regular tetrahedron with total area below $\sqrt{2}/2$ from a singular field
-- statement:
--   Throughout, a **cylinder** in $\mathbb{R}^3$ is given by a unit vector $a$ (its axis) and a base set $B$ contained in the plane $a^{\perp}$; it occupies the set $\{\,b+ta : b\in B,\ t\in\mathbb{R}\,\}$, and its **area** is the two-dimensional Lebesgue measure of $B$ in $a^{\perp}$. It is a *parallelogram cylinder* if $B=\{q+su+tv : 0\le s\le 1,\ 0\le t\le 1\}$, and a *triangle cylinder* if $B=\{q+su+tv : s,t\ge 0,\ s+t\le 1\}$, for some point $q$ and linearly independent vectors $u,v$. A union of cylinders below means the union of the sets they occupy.
--
--   Let
--
--   $$
--   T=\{\,(x,y,\sqrt{2}\,t) \;:\; 0\le t\le 1,\ |x|\le 1-t,\ |y|\le t\,\}
--   $$
--
--   be the regular tetrahedron of edge length $2$, with vertices $(\pm1,0,0)$ and $(0,\pm1,\sqrt2)$.
--
--   Fix real parameters $p$ and $\gamma$. For points $b=(b_1,b_2)$ of the plane with $b_2>0$ define the singular field $F=(F_1,F_2)$, the ceiling polynomial $P$, and for $c>0$ the compact domain $D_c$ by
--
--   $$
--   F(b)=\Bigl(\tfrac14\,(2b_2)^{p-1}\Bigl(p+(2-p)\frac{b_1^2}{b_2^2}\Bigr),\ (2b_2)^{p-2}\,b_1\Bigr),\qquad P(s)=\frac{p}{4}\,s^2+(2-p)\,s^4,
--   $$
--
--   $$
--   D_c=\Bigl\{\,b\in\mathbb{R}^2 \;:\; c^{\gamma}\le b_2\le 2,\ \ |b_1|\le b_2,\ \ b_2\le \tfrac12+c^2P(b_1)+c^{5/2}\,\Bigr\}.
--   $$
--
--   From these data define:
--
--   1. the lower ruled piece $L_c=\{(s,\ b_1+s\,cF_1(b),\ \sqrt2\,(b_2+s\,cF_2(b))) : b\in D_c,\ |s|\le 1\}$;
--   2. the upper ruled piece $U_c=\{(b_1-y\,cF_1(b),\ y,\ \sqrt2\,(1-b_2+y\,cF_2(b))) : b\in D_c,\ |y|\le 1\}$;
--   3. for $d\in\mathbb{R}$, the tips $\mathrm{Tip}^-_d=\{(x,y,\sqrt2\,t) : x\in\mathbb{R},\ 0\le t\le 2d,\ |y|\le t\}$ and $\mathrm{Tip}^+_d=\{(x,y,\sqrt2\,(1-s)) : y\in\mathbb{R},\ 0\le s\le 2d,\ |x|\le s\}$;
--   4. the cost $\mathrm{Cost}(c)=\sqrt2\displaystyle\int_{D_c}\frac{db}{\sqrt{1+c^2F_1(b)^2+2c^2F_2(b)^2}}$;
--   5. the coefficient $\kappa(p)=\bigl(\tfrac12\bigr)^4\,\dfrac{2p^2+10p-13}{30p}$.
--
--   **Theorem.** Let $p,\gamma\in\mathbb{R}$ satisfy
--
--   $$
--   1<p<\frac{\sqrt{51}-5}{2},\qquad 1<\gamma<\frac{1}{2-p}.
--   $$
--
--   Then:
--
--   1. $\kappa(p)<0$;
--   2. as $c\to0^+$,
--
--      $$
--      2\,\mathrm{Cost}(c)+8\sqrt2\,(c^{\gamma})^2=\frac{\sqrt2}{2}+2\sqrt2\,\kappa(p)\,c^2+o(c^2);
--      $$
--
--   3. there is $c_0>0$ such that for every $0<c<c_0$ there exist parallelogram cylinders $C_1,\dots,C_n$ and $C'_1,\dots,C'_m$ and triangle cylinders $B_1,B_2$ with $L_c\subseteq\bigcup_i C_i$, $U_c\subseteq\bigcup_j C'_j$, $B_1$ occupying exactly $\mathrm{Tip}^-_{c^\gamma}$, $B_2$ occupying exactly $\mathrm{Tip}^+_{c^\gamma}$, and
--
--      $$
--      T\subseteq\bigcup_{i=1}^{n}C_i\cup\bigcup_{j=1}^{m}C'_j\cup B_1\cup B_2,\qquad \sum_{i=1}^{n}\mathrm{area}(C_i)+\sum_{j=1}^{m}\mathrm{area}(C'_j)+\mathrm{area}(B_1)+\mathrm{area}(B_2)<\frac{\sqrt2}{2}.
--      $$
--
--   The admissible range of $p$ is non-empty but narrow, since $(\sqrt{51}-5)/2\approx 1.0707$; for such $p$ the range of $\gamma$ is a non-empty interval just above $1$.
--
--   The threshold $\sqrt2/2$ is the total area of the obvious two-cylinder cover of $T$: the triangular prisms $\{(x,y,\sqrt2\,t) : |y|\le t\le\frac12\}$ and $\{(x,y,\sqrt2\,(1-s)) : |x|\le s\le\frac12\}$ cover $T$ (according as $t\le\frac12$ or $t\ge\frac12$), and each has a cross-section of area $\sqrt2/4$. The sets $L_c$ and $U_c$ are ruled sets whose rulings are tilted away from these prisms by the small field $cF$, and the theorem asserts that $T$ admits a finite cover by parallelogram and triangle cylinders of total area strictly below $\sqrt2/2$, with the second-order expansion of the relevant cost having negative coefficient $2\sqrt2\,\kappa(p)$. It is the singular-field endpoint among the cylinder-covering statements of this development.
--
--   **Formalization Note** This is `SingularStatement`. Lean indexes coordinates from $0$, so $(b_1,b_2)$ is `(b 0, b 1)`, and the field is written with $b_2/(1/2)$ and $(1/2)/2$, i.e. $2b_2$ and $\frac14$. The powers $(2b_2)^{p-1}$, $c^{\gamma}$ and $c^{5/2}$ are real powers (`Real.rpow`); the field is defined on the whole plane with Lean's conventions for division by zero, but only its values on $D_c$, where $b_2\ge c^{\gamma}>0$, enter. The little-$o$ claim is `Asymptotics.IsLittleO` and the "for all sufficiently small $c$" claim is an eventual statement, both along the filter `nhdsWithin 0 (Ioi 0)`. Areas are `volume.real` of the base, and the two parallelogram families are indexed by `Fin n` and `Fin m`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Singular.lean#L67-L105

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
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration
import Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume
import Definitions.Def_OAI_Geometry_RuledCovering_CapAsymptotics
import Definitions.Def_OAI_Geometry_RuledCovering_SingularEnergy
import Definitions.Def_OAI_Geometry_RuledCovering_EnergyIntegral
import Definitions.Def_OAI_Geometry_RuledCovering_TipCylinders

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.singular : SingularStatement := by sorry
