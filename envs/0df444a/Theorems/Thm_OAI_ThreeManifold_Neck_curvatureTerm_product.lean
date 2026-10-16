-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Neck_curvatureTerm_product
-- name    : OAI.ThreeManifold.Neck.curvatureTerm_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:16:41.075262+00:00
-- url     : https://prove2.me/theorems/a83fb429-ef96-44f9-a3c5-cf88eaad1d42
-- title:
--   Curvature of a block metric $dt^2+Q(t)$ in coordinates
-- statement:
--   Let $M$ be a smooth 3-manifold modelled on $\mathbb{R}^3$ (coordinates indexed $0,1,2$), let $g$ be a smooth Riemannian metric on $M$, and let $c$ be an open partial homeomorphism from $M$ to $\mathbb{R}^3$. For $y\in\mathbb{R}^3$ let $G(y)_{ij}=g_{c^{-1}(y)}\bigl(d(c^{-1})_y e_i,\,d(c^{-1})_y e_j\bigr)$ be the coordinate metric matrix, and write $\partial_i$ for the partial derivative in direction $e_i$. The coordinate Christoffel symbols and curvature are
--   $$
--   \Gamma^i_{jk}=\tfrac12\sum_l(G^{-1})_{il}\bigl(\partial_jG_{lk}+\partial_kG_{lj}-\partial_lG_{jk}\bigr),\qquad
--   R^l_{kij}=\partial_i\Gamma^l_{jk}-\partial_j\Gamma^l_{ik}+\sum_m\bigl(\Gamma^l_{im}\Gamma^m_{jk}-\Gamma^l_{jm}\Gamma^m_{ik}\bigr),
--   $$
--   and the curvature term is $\mathcal{R}_c(y)(u,v,w)^l=\sum_{k,i,j}R^l_{kij}(y)\,w^ku^iv^j$.
--
--   On the model side, write elements of $\mathbb{R}\times\mathbb{R}^2$ as $U=(U^0,\bar U)$, put $\langle x,y\rangle_A=x^{\mathsf T}Ay$, and for $2\times2$ matrices $P,A,B$ let
--   $\Gamma_{P,A}(U,V)=\bigl(-\tfrac12\langle\bar U,\bar V\rangle_A,\ \tfrac12(U^0PA\bar V+V^0PA\bar U)\bigr)$,
--   $\Gamma'_{P,A,B}(U,V)=\bigl(-\tfrac12\langle\bar U,\bar V\rangle_B,\ \tfrac12(U^0S\bar V+V^0S\bar U)\bigr)$ with $S=PB-PAPA$, and
--   $\mathcal{R}_{P,A,B}(U,V,W)=U^0\Gamma'(V,W)-V^0\Gamma'(U,W)+\Gamma(U,\Gamma(V,W))-\Gamma(V,\Gamma(U,W))$.
--   Let $\sigma:\mathbb{R}^3\to\mathbb{R}\times\mathbb{R}^2$, $\sigma(y)=(y_0,(y_1,y_2))$, with inverse $\iota$.
--
--   **Theorem.** Let $Q,P,A:\mathbb{R}\to\mathbb{R}^{2\times2}$, $B\in\mathbb{R}^{2\times2}$ and $x\in\mathbb{R}^3$. Assume:
--
--   1. for all $y$ in a neighbourhood of $x$, $G(y)=\begin{pmatrix}1&0\\0&Q(y_0)\end{pmatrix}$ in block form;
--   2. for all $r$ in a neighbourhood of $x_0$, $Q$ is differentiable at $r$ with $Q'(r)=A(r)$, $Q(r)P(r)=I$, and $A(r)$ is symmetric;
--   3. $P$ is differentiable at $x_0$ with $P'(x_0)=-P(x_0)A(x_0)P(x_0)$;
--   4. $A$ is differentiable at $x_0$ with $A'(x_0)=B$.
--
--   Then for all $u,v,w\in\mathbb{R}^3$,
--   $$
--   \mathcal{R}_c(x)(u,v,w)=\iota\Bigl(\mathcal{R}_{P(x_0),A(x_0),B}\bigl(\sigma u,\sigma v,\sigma w\bigr)\Bigr).
--   $$
--
--   So for a metric of the form $dt^2+Q(t)_{ij}dx^idx^j$ in a chart, the curvature term at a point is given by an explicit formula in $Q^{-1}$, $\partial_tQ$ and $\partial_t^2Q$ at that height. This is the bridge between the abstract Jacobi equation of the main statement and the explicit neck computations.
--
--   **Formalization Note** $d(c^{-1})$ is Mathlib's manifold derivative `mfderiv`, partial derivatives are `fderiv` applied to basis vectors, and $G^{-1}$ is the matrix inverse. The partial homeomorphism $c$ need not belong to the atlas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L705-L736

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck

open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.Neck.curvatureTerm_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q P A : ℝ → TMat} {B : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hj : ∀ᶠ r in nhds (x 0), HasDerivAt Q (A r) r ∧ Q r * P r = 1 ∧ (A r)ᵀ = A r)
    (hP : HasDerivAt P (-P (x 0) * A (x 0) * P (x 0)) (x 0))
    (hA : HasDerivAt A B (x 0)) (u v w : E3) :
    curvatureTerm g c x u v w =
      joinVector (curvatureJet (P (x 0)) (A (x 0)) B
        (splitVector u) (splitVector v) (splitVector w)) := by sorry
