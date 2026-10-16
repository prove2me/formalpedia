-- Prove2me | Theorems.Thm_OAI_ThreeManifold_HyperbolicCore_action_orientation
-- name    : OAI.ThreeManifold.HyperbolicCore.action_orientation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:07:42.574445+00:00
-- url     : https://prove2.me/theorems/200fd8b1-fa71-43b5-9fc6-78dfd3571956
-- title:
--   Modular transformations preserve the orientation of the upper half-plane
-- statement:
--   Let $\mathbb{H}=\{z\in\mathbb{C}:\operatorname{Im}z>0\}$ carry its standard atlas as an open subset of $\mathbb{C}$: for every $a\in\mathbb{H}$ the chart $\varphi_a$ is the inclusion $\mathbb{H}\hookrightarrow\mathbb{C}$, whose image is the open upper half-plane. Let $g=\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix}\in SL(2,\mathbb{Z})$ act on $\mathbb{H}$ by $g\cdot z=\frac{\alpha z+\beta}{\gamma z+\delta}$.
--
--   For all $a,b\in\mathbb{H}$ and every $x$ in the image of $\varphi_a$, the map $y\mapsto\varphi_b(g\cdot\varphi_a^{-1}(y))$, viewed as a map $\mathbb{R}^2\to\mathbb{R}^2$, has positive Jacobian determinant at $x$:
--   $$
--   \det D\big(y\mapsto\varphi_b(g\cdot\varphi_a^{-1}(y))\big)(x)>0 .
--   $$
--
--   This is the orientation hypothesis needed to orient the atlas of a quotient $\mathbb{H}/\Gamma$ for a subgroup $\Gamma\le SL(2,\mathbb{Z})$; in the construction it is applied to the cusped surface $\mathbb{H}/\bar\Gamma$.
--
--   **Formalization Note** $D$ is the real Fréchet derivative (`fderiv ℝ`) of a map $\mathbb{C}\to\mathbb{C}$ and $\det$ is `LinearMap.det` of the resulting $\mathbb{R}$-linear map. The charts are Mathlib's `chartAt ℂ a` on `ℍ`; their inverse is defined on all of $\mathbb{C}$, but only its behaviour near $x$ matters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Gluing.lean#L1018-L1046

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing

open OAI OAI.ThreeManifold OAI.ThreeManifold.HyperbolicCore
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
open Set Filter Topology Manifold Matrix
open scoped ContDiff UpperHalfPlane MatrixGroups

theorem OAI.ThreeManifold.HyperbolicCore.action_orientation (g : SL(2,ℤ)) (a b : ℍ) (x : ℂ)
    (hx : x ∈ (chartAt ℂ a).target) :
    0 < LinearMap.det (fderiv ℝ
      (fun y => chartAt ℂ b (g • (chartAt ℂ a).symm y)) x).toLinearMap := by sorry
