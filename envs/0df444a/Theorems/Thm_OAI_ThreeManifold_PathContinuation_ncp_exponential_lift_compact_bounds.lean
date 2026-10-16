-- Prove2me | Theorems.Thm_OAI_ThreeManifold_PathContinuation_ncp_exponential_lift_compact_bounds
-- name    : OAI.ThreeManifold.PathContinuation.ncp_exponential_lift_compact_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:58:26.291341+00:00
-- url     : https://prove2.me/theorems/9594ef01-15f4-4e7c-82bc-89e167ca907f
-- title:
--   Lifts of a $C^1$ curve through the exponential map of a metric without conjugate points stay in a compact set on bounded time intervals
-- statement:
--   Let $M$ be a compact Hausdorff smooth 3-manifold (modelled on $\mathbb{R}^3$) with a smooth Riemannian metric $g$ that has *no conjugate points*. This means: for every open set $U\subseteq\mathbb{R}$ that is an interval, every smooth geodesic $\gamma$ on $U$ and every Jacobi field $J$ along $\gamma$ on $U$, if $J(a)=0=J(b)$ for two distinct $a,b\in U$, then $J$ vanishes on all of $U$. Fix $p\in M$ and identify $T_pM$ with $\mathbb{R}^3$. Let $\exp_p:\mathbb{R}^3\to M$ be the exponential map, $\exp_p(v)=\sigma_v(1)$, where $\sigma_v$ is the geodesic with $\sigma_v(0)=p$ and $\sigma_v'(0)=v$. Under the no-conjugate-points hypothesis $\exp_p$ is a local homeomorphism.
--
--   Let $\gamma:\mathbb{R}\to M$ be a $C^1$ curve and consider the *lifting state space*
--   $$
--   \mathcal{S} = \{(t,v)\in\mathbb{R}\times\mathbb{R}^3 : \exp_p(v) = \gamma(t)\}
--   $$
--   with the subspace topology. For an open interval $I$, a *lift on $I$* is a map $z:\mathbb{R}\to\mathcal{S}$ such that at every $s\in I$ the map $z$, viewed in $\mathbb{R}\times\mathbb{R}^3$, is differentiable with derivative of the form $(1,w)$ for some $w\in\mathbb{R}^3$. Thus its time component advances with unit speed while its vector component lifts $\gamma$ through $\exp_p$.
--
--   **Theorem.** For every point $x\in\mathcal{S}$ and every $A>0$ there is a compact set $K\subseteq\mathcal{S}$ such that
--   $$
--   \forall a\in(0,A],\ \ \forall z \text{ a lift on } (-a,a) \text{ with } z(0)=x:\qquad z\big((-a,a)\big)\subseteq K .
--   $$
--
--   This is the a-priori bound showing that lifts of curves through $\exp_p$ cannot escape to infinity in finite time. Together with local existence and uniqueness of lifts, it gives global path lifting and hence that $\exp_p$ is a covering map, which is the conclusion of the Cartan–Hadamard theorem in the setting of metrics without conjugate points.
--
--   **Formalization Note** The state space is `State (exponential g p) γ` and lifts are curves of `equation (exponential g p) γ (exponential_isLocalHomeomorph g hn p)` on `Ioo (-a) a`. The local-homeomorphism proof is a parameter of this equation; it is used only for uniqueness of solutions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Continuation.lean#L504-L577

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

open OAI OAI.ThreeManifold OAI.ThreeManifold.PathContinuation
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
open RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M] {γ : ℝ → M}

theorem OAI.ThreeManifold.PathContinuation.ncp_exponential_lift_compact_bounds (g : SmoothMetric M)
    (hn : NoConjugatePoints g) (p : M)
    (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 1 γ) (x : State (exponential g p) γ)
    (A : ℝ) (_hA : 0 < A) :
    ∃ K : Set (State (exponential g p) γ), IsCompact K ∧ ∀ z a,
      0 < a → a ≤ A → z 0 = x →
      (equation (exponential g p) γ (exponential_isLocalHomeomorph g hn p)).CurveOn z (Ioo (-a) a) →
      MapsTo z (Ioo (-a) a) K := by sorry
