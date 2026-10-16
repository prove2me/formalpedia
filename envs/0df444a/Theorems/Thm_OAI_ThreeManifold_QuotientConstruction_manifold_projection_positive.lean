-- Prove2me | Theorems.Thm_OAI_ThreeManifold_QuotientConstruction_manifold_projection_positive
-- name    : OAI.ThreeManifold.QuotientConstruction.manifold_projection_positive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:06:22.0807+00:00
-- url     : https://prove2.me/theorems/72150774-44d2-4676-94b3-e8ecce22ff43
-- title:
--   A covering projection is orientation preserving in the induced charts
-- statement:
--   Let $E$ be a real normed space, $M$ a topological space with an atlas modelled on $E$ ($\varphi_a$ denotes the chosen chart at $a\in M$), $G$ a group acting on $M$, and $p:M\to Q$ a quotient covering map for this action: $p$ is a quotient map, each $k\in G$ acts continuously, $p(x)=p(y)$ exactly when $x=k\cdot y$ for some $k\in G$, and every point has a neighbourhood $U$ with $k\cdot U\cap U\ne\emptyset$ only for $k=1$. Let $\sigma:Q\to M$ satisfy $p\circ\sigma=\mathrm{id}_Q$ and give $Q$ the induced atlas whose chart at $b\in Q$ is $\psi_b=\varphi_{\sigma(b)}\circ\lambda_b$, $\lambda_b$ being the local inverse of $p$ through $\sigma(b)$.
--
--   Assume that each map $x\mapsto k\cdot x$ is continuous and that for all $k\in G$, $a,b\in M$ and $x\in\varphi_a(\operatorname{dom}\varphi_a)$ with $k\cdot\varphi_a^{-1}(x)\in\operatorname{dom}\varphi_b$ one has $\det D\big(y\mapsto\varphi_b(k\cdot\varphi_a^{-1}(y))\big)(x)>0$. Then for every $a\in M$, every $b\in Q$ and every $x\in\varphi_a(\operatorname{dom}\varphi_a)$ with $p(\varphi_a^{-1}(x))\in\operatorname{dom}\psi_b$,
--   $$
--   \det D\big(y\mapsto\psi_b(p(\varphi_a^{-1}(y)))\big)(x)>0 .
--   $$
--
--   In words, the covering projection $p$ is orientation preserving when written in the charts of $M$ and the induced charts of $Q$. This is the form in which the orientation behaviour of a covering projection enters later chart computations, where transition maps are written in covering coordinates.
--
--   **Formalization Note** $D$ is `fderiv ℝ` and $\det$ is `LinearMap.det`; Mathlib sets the derivative of a non-differentiable map to $0$. The atlas on $Q$ is `manifoldCharts hp hσ`, introduced by a `let` in the statement; no smoothness of $M$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Gluing.lean#L987-L1013

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing

open OAI OAI.ThreeManifold OAI.ThreeManifold.QuotientConstruction
open Set Manifold Bundle
open scoped ContDiff
open Set Filter Topology Manifold
open scoped ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Set Pointwise
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology TopologicalSpace CategoryTheory
open Set Topology TopologicalSpace
open Set Topology Filter Manifold
open scoped ContDiff
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff UpperHalfPlane MatrixGroups
open Set Topology Filter TopologicalSpace Manifold IsManifold
open scoped ContDiff
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff
open Set Topology Filter Manifold IsManifold
open scoped ContDiff
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]
  [Group G] [MulAction G M] {p : M → Q} (hp : IsQuotientCoveringMap p G)

theorem OAI.ThreeManifold.QuotientConstruction.manifold_projection_positive {σ : Q → M} (hσ : Function.RightInverse σ p)
    (hact : ∀ k : G, Continuous (fun x : M => k • x))
    (hpos : ∀ (k : G) (a b : M) (x : E), x ∈ (chartAt E a).target →
      k • (chartAt E a).symm x ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (k • (chartAt E a).symm y)) x).toLinearMap) :
    let := manifoldCharts (E := E) hp hσ
    ∀ (a : M) (b : Q) (x : E), x ∈ (chartAt E a).target →
      p ((chartAt E a).symm x) ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (p ((chartAt E a).symm y))) x).toLinearMap := by sorry
