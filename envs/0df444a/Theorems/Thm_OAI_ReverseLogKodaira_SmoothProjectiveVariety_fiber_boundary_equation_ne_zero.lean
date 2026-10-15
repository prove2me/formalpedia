-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_fiber_boundary_equation_ne_zero
-- name    : OAI.ReverseLogKodaira.SmoothProjectiveVariety.fiber_boundary_equation_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:04:23.18798+00:00
-- url     : https://prove2.me/theorems/251726ef-06f8-49d0-8beb-76a62d1c253b
-- title:
--   A local equation of the boundary restricts to a nonzero rational function on every fibre model
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; $K(Z)$ denotes its function field and $\mathcal{O}_Z(W)$ the ring of sections over an open set $W$. A *reduced simple normal crossing (SNC) boundary* $E$ on $Z$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim Z-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_Z(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$.
--
--   Let $(X,E)$ and $(Y,D)$ be smooth projective varieties with reduced SNC boundaries. A *boundary fibration* $f\colon(X,E)\to(Y,D)$ is a surjective morphism $f\colon X\to Y$ over $\mathbb{C}$ whose fibres $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$ over all complex points $y$ are connected and which satisfies $f^{-1}(\operatorname{Supp}D)\subseteq\operatorname{Supp}E$; no smoothness is assumed. A *complex point* $y\in Y(\mathbb{C})$ is a section $\operatorname{Spec}\mathbb{C}\to Y$ of the structure morphism; we write $y\in U$ when its image point lies in $U$. A *fibre model* of $f$ over $y$ is a triple $(F,i,E_F)$ consisting of a smooth projective variety $F$, a morphism $i\colon F\to X$ such that $F$, together with $i$ and its structure morphism, is a fibre product $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$, and a reduced SNC boundary $E_F$ on $F$ whose ideal sheaf is the pullback $i^{-1}\mathcal{I}_E\cdot\mathcal{O}_F$. For an open set $V\subseteq X$ that meets the fibre, i.e. $i^{-1}(V)\neq\emptyset$, and for $g\in\mathcal{O}_X(V)$, write $g|_F\in K(F)$ for the image of $i^{*}g\in\mathcal{O}_F(i^{-1}(V))$ in the function field of $F$ (its germ at the generic point of $F$).
--
--   Let $f\colon(X,E)\to(Y,D)$ be a boundary fibration, $y\in Y(\mathbb{C})$ a complex point and $(F,i,E_F)$ a fibre model of $f$ over $y$. Let $V\subseteq X$ be an affine open that meets the fibre, i.e. $i^{-1}(V)\neq\emptyset$, and let $t\in\mathcal{O}_X(V)$ generate the boundary ideal on $V$, i.e. $\mathcal{I}_E(V)=(t)$. Then
--
--   $$
--   t|_F\neq0\qquad\text{in }K(F).
--   $$
--
--   Geometrically, a local equation of the boundary of $X$ never vanishes identically on a fibre model that meets the chart; in particular $i(F)\not\subseteq\operatorname{Supp}E$. This guarantees that the denominators $(t|_F)^{-m}$ used to restrict logarithmic pluricanonical forms from $X$ to a fibre are genuine inverses in $K(F)$.
--
--   **Formalization Note** The element $t|_F$ is `chartToFunctionField F.inclusion V t`, and the boundary ideal on $V$ is `E.ideal.ideal V`. The hypothesis $t\neq0$ is not assumed; it follows from the conclusion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/BoundaryPullback.lean#L74-L120

import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem OAI.ReverseLogKodaira.SmoothProjectiveVariety.fiber_boundary_equation_ne_zero
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (V : X.scheme.affineOpens) [Nonempty (F.inclusion ⁻¹ᵁ V.1)]
    (t : Γ(X.scheme, V.1)) (hEt : E.ideal.ideal V = Ideal.span {t}) :
    chartToFunctionField F.inclusion V.1 t ≠ 0 := by sorry
