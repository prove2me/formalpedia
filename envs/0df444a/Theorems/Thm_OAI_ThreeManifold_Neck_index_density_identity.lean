-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Neck_index_density_identity
-- name    : OAI.ThreeManifold.Neck.index_density_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:13:48.419484+00:00
-- url     : https://prove2.me/theorems/739808b3-d2e4-4ac8-9792-e9459bc0b5e1
-- title:
--   Pointwise index-form identity for a metric $dt^2+Q(t)$
-- statement:
--   For a real $2\times 2$ matrix $A$ and $u,v\in\mathbb{R}^2$ write $\langle u,v\rangle_A = u^{\mathsf T}Av$. Elements of $\mathbb{R}\times\mathbb{R}^2$ are written $U=(U^0,\bar U)$ with $U^0\in\mathbb{R}$ and $\bar U\in\mathbb{R}^2$. For real $2\times2$ matrices $P,Q,A,B$ define:
--
--   - the metric $g_Q(U,V)=U^0V^0+\langle\bar U,\bar V\rangle_Q$;
--   - the connection term $\Gamma_{P,A}(U,V) = \bigl(-\tfrac12\langle\bar U,\bar V\rangle_A,\ \tfrac12\,(U^0\,PA\bar V + V^0\,PA\bar U)\bigr)$;
--   - the derivative term $\Gamma'_{P,A,B}(U,V)=\bigl(-\tfrac12\langle\bar U,\bar V\rangle_B,\ \tfrac12\,(U^0\,S\bar V+V^0\,S\bar U)\bigr)$ with $S=PB-PAPA$;
--   - the curvature term $\mathcal{R}(U,V,W)=U^0\,\Gamma'_{P,A,B}(V,W)-V^0\,\Gamma'_{P,A,B}(U,W)+\Gamma_{P,A}(U,\Gamma_{P,A}(V,W))-\Gamma_{P,A}(V,\Gamma_{P,A}(U,W))$;
--   - the energy density $e(T,V,\dot V)=(\dot V^0)^2+\langle\dot{\bar V},\dot{\bar V}\rangle_Q+2V^0\langle\dot{\bar V},\bar T\rangle_A+\tfrac12(V^0)^2\langle\bar T,\bar T\rangle_B$;
--   - the boundary jet
--
--   $$
--   \begin{aligned}
--   b_{P,A,B}(T,V,\dot V) ={}& -\tfrac14\langle\bar T,\bar T\rangle_A\langle\bar V,\bar V\rangle_A - T^0\langle\dot{\bar V},\bar V\rangle_A - \tfrac12 (T^0)^2\langle\bar V,\bar V\rangle_B \\
--   &+ \dot V^0\langle\bar V,\bar T\rangle_A + V^0\langle\dot{\bar V},\bar T\rangle_A + V^0T^0\langle\bar V,\bar T\rangle_B - V^0T^0\langle\bar V,\bar T\rangle_{APA}.
--   \end{aligned}
--   $$
--
--   **Theorem.** Assume $QP=I$ and that $Q$, $P$, $A$, $B$ are symmetric. Then for all $T,V,\dot V\in\mathbb{R}\times\mathbb{R}^2$,
--   $$
--   g_Q\bigl(\dot V+\Gamma_{P,A}(T,V),\,\dot V+\Gamma_{P,A}(T,V)\bigr)-g_Q\bigl(V,\mathcal{R}(V,T,T)\bigr)=e(T,V,\dot V)-b_{P,A,B}(T,V,\dot V).
--   $$
--
--   These are the coordinate expressions, at one point, for a metric $dt^2+Q(t)_{ij}\,dx^i dx^j$ on $\mathbb{R}\times\mathbb{R}^2$ with $P=Q^{-1}$, $A=\partial_tQ$ and $B=\partial_t^2Q$. Then $\Gamma_{P,A}$ is the Christoffel contraction, $\dot V+\Gamma(T,V)$ is the covariant derivative of a field $V$ along a curve with velocity $T$, and $\mathcal{R}$ is the curvature term. The left side is the integrand of the index form. The identity rewrites it as an explicit energy density minus a term $b$, which is shown separately to be an exact derivative along geodesics.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L258-L274

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

theorem OAI.ThreeManifold.Neck.index_density_identity {P Q A B : TMat} (hQP : Q * P = 1)
    (hQ : Qᵀ = Q) (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B) (T V Vdot : Vec) :
    metric Q (Vdot + gamma P A T V) (Vdot + gamma P A T V) -
      metric Q V (curvatureJet P A B V T T) =
        coordinateEnergyDensity Q A B T V Vdot - boundaryJet P A B T V Vdot := by sorry
