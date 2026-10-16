-- Prove2me | Theorems.Thm_OAI_ThreeManifold_QuotientConstruction_manifold_quotient_positive
-- name    : OAI.ThreeManifold.QuotientConstruction.manifold_quotient_positive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:05:34.009315+00:00
-- url     : https://prove2.me/theorems/8f367ee5-c61c-4489-af06-1e3c62a75734
-- title:
--   Orientation of the quotient atlas from orientation-preserving deck transformations
-- statement:
--   Let $E$ be a real normed space and $M$ a topological space with an atlas modelled on $E$; for $a\in M$ write $\varphi_a$ for the chosen chart at $a$, with domain $\operatorname{dom}\varphi_a\subset M$ and image $\varphi_a(\operatorname{dom}\varphi_a)\subset E$. Let a group $G$ act on $M$, and let $p:M\to Q$ be a quotient covering map for this action: $p$ is a quotient map, each $k\in G$ acts continuously, $p(x)=p(y)$ exactly when $x=k\cdot y$ for some $k\in G$, and every point of $M$ has a neighbourhood $U$ such that $k\cdot U\cap U\ne\emptyset$ only for $k=1$. Let $\sigma:Q\to M$ be any map with $p\circ\sigma=\mathrm{id}_Q$, and equip $Q$ with the induced atlas, whose chart at $q\in Q$ is $\psi_q=\varphi_{\sigma(q)}\circ\lambda_q$, where $\lambda_q$ is the local inverse of $p$ through $\sigma(q)$.
--
--   Assume that every map $x\mapsto k\cdot x$ ($k\in G$) is continuous, and that the deck transformations are orientation preserving in the charts of $M$: for all $k\in G$, $a,b\in M$ and $x\in\varphi_a(\operatorname{dom}\varphi_a)$ with $k\cdot\varphi_a^{-1}(x)\in\operatorname{dom}\varphi_b$,
--   $$
--   \det D\big(y\mapsto\varphi_b(k\cdot\varphi_a^{-1}(y))\big)(x)>0 .
--   $$
--   Then the induced atlas on $Q$ is positively oriented: for any two charts $\psi,\psi'$ of this atlas and every $x\in\psi(\operatorname{dom}\psi)$ with $\psi^{-1}(x)\in\operatorname{dom}\psi'$,
--   $$
--   \det D(\psi'\circ\psi^{-1})(x)>0 .
--   $$
--
--   This is the orientation part of the construction of a manifold as a quotient by a covering action: it reduces the orientability of the quotient atlas to a check on the twisted transition maps of the cover, for example for the cusped surface $\mathbb{H}/\bar\Gamma$, whose deck transformations are orientation preserving Möbius maps.
--
--   **Formalization Note** $D$ is the Fréchet derivative `fderiv ℝ` and $\det$ is `LinearMap.det`; with Mathlib's conventions the derivative of a non-differentiable function is $0$, so the positivity hypotheses also force differentiability at the relevant points (when $E\ne0$). No smoothness of $M$ is assumed. The induced atlas is `manifoldCharts hp hσ` and the conclusion is `AtlasOrientation.Positive` for it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Gluing.lean#L949-L985

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

theorem OAI.ThreeManifold.QuotientConstruction.manifold_quotient_positive {σ : Q → M} (hσ : Function.RightInverse σ p)
    (hact : ∀ k : G, Continuous (fun x : M => k • x))
    (hpos : ∀ (k : G) (a b : M) (x : E), x ∈ (chartAt E a).target →
      k • (chartAt E a).symm x ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (k • (chartAt E a).symm y)) x).toLinearMap) :
    let := manifoldCharts (E := E) hp hσ
    AtlasOrientation.Positive (E := E) (M := Q) := by sorry
