-- Prove2me | Theorems.Thm_OAI_ThreeManifold_GluedConstruction_coverChart_component_smooth
-- name    : OAI.ThreeManifold.GluedConstruction.coverChart_component_smooth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:09:20.488577+00:00
-- url     : https://prove2.me/theorems/d0865975-013e-4a3c-9dd6-2a59721eaaaa
-- title:
--   Smoothness of the surface and circle components of the lifted product charts
-- statement:
--   Let $\Sigma=\mathbb{H}/\bar\Gamma$ be the cusped hyperbolic surface, with covering projection $\pi:\mathbb{H}\to\Sigma$ and its smooth atlas modelled on $\mathbb{C}$ (charts $\varphi_x$, $x\in\Sigma$); let $S^1=\mathbb{R}/6\mathbb{Z}$ with its smooth atlas modelled on $\mathbb{R}$ (charts $\chi_u$, $u\in S^1$) and projection $t\mapsto[t]$. The piece is $X=\{x\in\Sigma:h(x)<\log8\}\times S^1$, where $h$ is the height function on $\Sigma$. Let $\mathrm{oc}:\mathbb{C}\to\mathbb{H}$ be the inverse of the inclusion $\mathbb{H}\hookrightarrow\mathbb{C}$ (it is the identity on the upper half-plane; its values elsewhere are irrelevant here).
--
--   Let $b=(x_b,u_b)\in X$, $z\in\mathbb{H}$ and $r\in\mathbb{R}$, and assume $\pi(z)\in\operatorname{dom}\varphi_{x_b}$ and $[r]\in\operatorname{dom}\chi_{u_b}$. Then both components of the lifted chart are $C^\infty$:
--
--   1. the map $\mathbb{C}\to\mathbb{C}$, $y\mapsto\varphi_{x_b}\big(\pi(\mathrm{oc}(y))\big)$, is $C^\infty$ in the real sense at the point $z$;
--   2. the map $\mathbb{R}\to\mathbb{R}$, $t\mapsto\chi_{u_b}([t])$, is $C^\infty$ at $r$.
--
--   In short,
--   $$
--   y\mapsto\varphi_{x_b}(\pi(\mathrm{oc}(y)))\ \text{is } C^\infty \text{ at } z,\qquad t\mapsto\chi_{u_b}([t])\ \text{is } C^\infty \text{ at } r .
--   $$
--
--   These are the two components of the chart of the piece $X$ (a product chart) read through the coverings $\mathbb{H}\to\Sigma$ and $\mathbb{R}\to S^1$. They are used to compute transition maps of the glued manifold in covering coordinates, for example when checking that its atlas is oriented.
--
--   **Formalization Note** $\mathrm{oc}$ is `UpperHalfPlane.ofComplex`; smoothness is `ContDiffAt ℝ ∞`, where `∞` means $C^\infty$. The chart of $X$ at $b$ is a product of the charts at the underlying surface point `b.1.1` and circle point `b.2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Gluing.lean#L1114-L1131

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing

open OAI OAI.ThreeManifold OAI.ThreeManifold.GluedConstruction
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
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
open HyperbolicCore

theorem OAI.ThreeManifold.GluedConstruction.coverChart_component_smooth (b : Piece) (z : ℍ) (r : ℝ)
    (hz : projection z ∈ (chartAt ℂ b.1.1).source)
    (hr : (r : Circle) ∈ (chartAt ℝ b.2).source) :
    ContDiffAt ℝ ∞ (fun y : ℂ => chartAt ℂ b.1.1 (projection (UpperHalfPlane.ofComplex y))) (z : ℂ) ∧
    ContDiffAt ℝ ∞ (fun t : ℝ => chartAt ℝ b.2 (t : Circle)) r := by sorry
