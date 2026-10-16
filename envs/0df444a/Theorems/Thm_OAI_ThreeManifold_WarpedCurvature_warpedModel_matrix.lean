-- Prove2me | Theorems.Thm_OAI_ThreeManifold_WarpedCurvature_warpedModel_matrix
-- name    : OAI.ThreeManifold.WarpedCurvature.warpedModel_matrix
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:54:14.229839+00:00
-- url     : https://prove2.me/theorems/5ce32e73-744a-4f25-867c-3ae3ed602155
-- title:
--   Gram matrix of the warped model metric $dt^2 + r(t)^2\,d\theta^2 + b^2\,d\varphi^2$ on $\mathbb{R}^3$
-- statement:
--   Let $r:\mathbb{R}\to\mathbb{R}$ be a $C^\infty$ function with $r(t)\neq 0$ for all $t$, and let $b\neq 0$ be a real number. The *warped model metric* $g^{r,b}$ is the smooth Riemannian metric on $\mathbb{R}^3$ (coordinates $x=(x_0,x_1,x_2)$, viewed as a manifold with its identity chart) given by
--   $g^{r,b}_x(u,v) = \langle T_x u, T_x v\rangle$, where $\langle\cdot,\cdot\rangle$ is the standard inner product and $T_x(v) = (v_0,\ r(x_0)\,v_1,\ b\,v_2)$; explicitly $g^{r,b}_x(u,v) = u_0v_0 + r(x_0)^2u_1v_1 + b^2u_2v_2$.
--
--   **Theorem.** For every $x\in\mathbb{R}^3$, the Gram matrix of $g^{r,b}$ at $x$ in the identity chart, i.e. the matrix with entries $g^{r,b}_x(e_i,e_j)$ for the standard basis vectors $e_0,e_1,e_2$, is
--   $$
--   \big(g^{r,b}_x(e_i,e_j)\big)_{i,j=0}^{2} \;=\; \begin{pmatrix} 1 & 0 & 0\\ 0 & r(x_0)^2 & 0 \\ 0 & 0 & b^2\end{pmatrix}
--   = \begin{pmatrix} 1 & 0\\ 0 & Q(x_0)\end{pmatrix},\qquad Q(t)=\begin{pmatrix} r(t)^2 & 0\\ 0 & b^2\end{pmatrix}.
--   $$
--
--   This identifies the warped model with a metric of block form $1\oplus Q(t)$ depending only on the first coordinate $t=x_0$, so that general curvature formulas for such block metrics apply to it. It is the coordinate description of the warped product $dt^2 + r(t)^2\,d\theta^2 + b^2\,d\varphi^2$.
--
--   **Formalization Note** In Lean the metric is `warpedModel hs hb hr`, built as a special case of a "triangular" metric $u_0v_0 + r^2(u_1-cu_2)(v_1-cu_2) + s^2u_2v_2$ with shear $c=0$ and $s=b$; the right-hand side is `Neck.blockMatrix (Q r b (x 0))`, where `blockMatrix` places a $2\times 2$ matrix in the lower-right block and `Q r b t = diag (r t ^ 2) (b ^ 2)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Curvature.lean#L626-L640

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature

open OAI OAI.ThreeManifold OAI.ThreeManifold.WarpedCurvature
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
open MetricConstruction CylinderConstruction RiemannianCoordinates
variable {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) {b : ℝ} (hb : b ≠ 0) (hr : ∀ t, r t ≠ 0)

theorem OAI.ThreeManifold.WarpedCurvature.warpedModel_matrix (x : E3) :
    metricMatrix (warpedModel hs hb hr) (OpenPartialHomeomorph.refl E3) x =
      Neck.blockMatrix (Q r b (x 0)) := by sorry
