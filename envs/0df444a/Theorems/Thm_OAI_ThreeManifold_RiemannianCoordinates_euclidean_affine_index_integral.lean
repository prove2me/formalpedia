-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_euclidean_affine_index_integral
-- name    : OAI.ThreeManifold.RiemannianCoordinates.euclidean_affine_index_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:04:06.842161+00:00
-- url     : https://prove2.me/theorems/22b056c3-def9-43b0-8a05-adfc06a16a83
-- title:
--   Change of variables for the index integral under an affine reparametrization
-- statement:
--   Let $g$ be any smooth Riemannian metric on $\mathbb R^3$, regarded as a smooth manifold with its single identity chart, so that tangent vectors are elements of $\mathbb R^3$. For a curve $\gamma:\mathbb R\to\mathbb R^3$ and a vector field $J:\mathbb R\to\mathbb R^3$ along it, the index density is
--   $$\mathcal I_{\gamma,J}(s)=g_{\gamma(s)}\big(\nabla_sJ,\nabla_sJ\big)-g_{\gamma(s)}\big(R(J,\dot\gamma)\dot\gamma,J\big),\qquad \nabla_sJ=\dot J+\Gamma_{\gamma}(\dot\gamma,J),$$
--   with $\Gamma$ the Christoffel term and $R$ the Riemann curvature tensor of $g$ (convention $R(\partial_i,\partial_j)\partial_k=\nabla_i\nabla_j\partial_k-\nabla_j\nabla_i\partial_k$).
--
--   **Statement.** Let $U\subseteq\mathbb R$ be open, let $\gamma$ be $C^\infty$ on $U$ and let $J$ be smooth along $\gamma$ on $U$ (that is, $C^\infty$ on $U$). Let $a,k,u,v\in\mathbb R$ with $k\ne0$ and $a+ks\in U$ for every $s$ between $u$ and $v$. Writing $\gamma_{a,k}(s)=\gamma(a+ks)$ and $J_{a,k}(s)=J(a+ks)$, one has
--   $$\int_u^v\mathcal I_{\gamma_{a,k},J_{a,k}}(s)\,ds\;=\;k\int_{a+ku}^{a+kv}\mathcal I_{\gamma,J}(\sigma)\,d\sigma,$$
--   with oriented integrals.
--
--   No geodesic assumption is needed. The formula transports index estimates between a geodesic and its affine reparametrizations: with $k>0$ it relates an arbitrary constant-speed geodesic to its unit-speed version, and with $k=-1$ it reverses the direction of travel.
--
--   **Formalization Note** The hypothesis on $\gamma$ is `ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U`, the field hypothesis is `SmoothFieldOn γ J U`, the range condition is stated over `uIcc u v`, and $\mathcal I$ is `indexPairDensity`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean#L1384-L1401

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
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages
import Definitions.Def_OAI_Geometry_ConjugatePoints_NoConjugatePoints

open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
open CompactMetric

theorem OAI.ThreeManifold.RiemannianCoordinates.euclidean_affine_index_integral (g : SmoothMetric E3) {γ J : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hJ : SmoothFieldOn γ J U) {a k u v : ℝ} (hk : k ≠ 0)
    (hd : ∀ s ∈ uIcc u v, a+k*s ∈ U) :
    (∫ s in u..v, indexPairDensity g (fun r => γ (a+k*r))
      (fun r => J (a+k*r)) (fun r => J (a+k*r)) s) =
      k * ∫ s in (a+k*u)..(a+k*v), indexPairDensity g γ J J s := by sorry
