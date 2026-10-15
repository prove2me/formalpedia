-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_projectionBody_eq_zonotope
-- name    : OAI.ProjectionCounterexample.projectionBody_eq_zonotope
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:02:03.629728+00:00
-- url     : https://prove2.me/theorems/0a0cc01d-b8b9-420e-9fb4-5e4e6d1715a8
-- title:
--   A cube-plus-diagonal brightness formula identifies the projection body as a zonotope
-- statement:
--   Let $d\in\mathbb{N}$ and equip $\mathbb{R}^d$ with the standard inner product. For a set $P\subseteq\mathbb{R}^d$ and a unit vector $u$, let $\pi_u$ be the orthogonal projection onto the hyperplane $u^{\perp}$ and let
--   $\operatorname{vol}_{d-1}(P\,|\,u^{\perp})=\mathcal{H}^{d-1}\bigl(\pi_u(P)\bigr)$
--   be the projection volume, where $\mathcal{H}^{d-1}$ is the $(d-1)$-dimensional Hausdorff measure normalized to agree with Lebesgue measure on $(d-1)$-dimensional affine subspaces. The projection body of $P$ is
--   $\Pi P=\{x\in\mathbb{R}^d:\ \langle u,x\rangle\le\operatorname{vol}_{d-1}(P\,|\,u^{\perp})\ \text{for all } u \text{ with } \|u\|=1\}$.
--
--   Let $Z_d$ be the Minkowski sum of the unit cube $[0,1]^d$ and the diagonal segment $\{t(1,\dots,1): 0\le t\le1\}$, translated by $-(1,\dots,1)$ so that it is centered at the origin; equivalently $Z_d=\{y\in\mathbb{R}^d: |y_i|\le1 \text{ and } |y_i-y_j|\le1 \text{ for all } i,j\}$. Its support function is
--   $h(u)=\tfrac12\bigl(\sum_{i=1}^d|u_i|+|\sum_{i=1}^d u_i|\bigr)$.
--
--   **Theorem.** Let $P\subseteq\mathbb{R}^d$ be any set and let $c>0$. If $\operatorname{vol}_{d-1}(P\,|\,u^{\perp})=c\,h(u)$ for every unit vector $u\in\mathbb{R}^d$, then
--
--   $$
--   \Pi P=c\,Z_d=\{c\,y:\ y\in Z_d\}.
--   $$
--
--   In words: a body whose brightness function is a positive multiple of the support function of the cube-plus-diagonal zonotope has that scaled zonotope as its projection body, so its volume can be computed from the zonotope. In the counterexample to the maximality of the simplex this is applied to the simplex $T_{20}=\operatorname{conv}\{0,e_1,\dots,e_{20}\}\subset\mathbb{R}^{20}$, whose brightness function is $h(u)/19!$, giving $\Pi T_{20}=Z_{20}/19!$.
--
--   **Formalization Note** $P$ is an arbitrary subset of `E d = EuclideanSpace ℝ (Fin d)`; no convexity, compactness or measurability is required, since the brightness formula is a hypothesis. The projection volume `projectionVolume P u` is the real number (`toReal`) of `μHE[d - 1]` of the projected set, with natural-number subtraction in $d-1$. The zonotope $c\,Z_d$ is `DiagonalZonotope.euclidean c`, the image of `DiagonalZonotope.centered` under $y\mapsto c\,y$ transported to Euclidean space, and $h$ is `DiagonalZonotope.support`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ZonotopeBridge.lean#L18-L43

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Definitions.Def_ProjectionCounterexample
import Definitions.Def_OAI_Geometry_ProjectionBody_GeometryDefinitions
import Definitions.Def_OAI_Geometry_ProjectionBody_ConvexGeometry
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCover
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCoordinates
import Definitions.Def_OAI_Geometry_ProjectionBody_GraphChart
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacetCharts
import Definitions.Def_OAI_Geometry_Zonotope_Decomposition
import Definitions.Def_OAI_Geometry_Zonotope_Support
import Definitions.Def_OAI_Geometry_Zonotope_Euclidean
import Definitions.Def_OAI_Geometry_Zonotope_Product
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetCharts
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetGraphs
import Definitions.Def_OAI_Geometry_ProjectionBody_HyperplaneJacobian
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionBody_ProjectionKernel

open OAI OAI.ProjectionCounterexample
open Set
open scoped RealInnerProductSpace

theorem OAI.ProjectionCounterexample.projectionBody_eq_zonotope {d : ℕ} (P : Set (E d)) (c : ℝ) (hc : 0 < c)
    (hbrightness : ∀ u : E d, ‖u‖ = 1 →
      projectionVolume P u = c * DiagonalZonotope.support (WithLp.ofLp u)) :
    projectionBody P = DiagonalZonotope.euclidean c := by sorry
