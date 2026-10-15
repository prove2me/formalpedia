-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_projectionBody_eq_productZonotope
-- name    : OAI.ProjectionCounterexample.projectionBody_eq_productZonotope
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:02:36.1308+00:00
-- url     : https://prove2.me/theorems/70039fc8-7172-443a-8659-3a74ec294ec1
-- title:
--   A block brightness formula identifies the projection body as a product of two zonotopes
-- statement:
--   Let $n,m\in\mathbb{N}$ and equip $\mathbb{R}^{n+m}$ with the standard inner product. For a set $P\subseteq\mathbb{R}^{n+m}$ and a unit vector $u$, let $\pi_u$ be the orthogonal projection onto the hyperplane $u^{\perp}$, let
--   $\operatorname{vol}_{n+m-1}(P\,|\,u^{\perp})=\mathcal{H}^{n+m-1}\bigl(\pi_u(P)\bigr)$
--   be the projection volume, where $\mathcal{H}^{n+m-1}$ is the $(n+m-1)$-dimensional Hausdorff measure normalized to agree with Lebesgue measure on $(n+m-1)$-dimensional affine subspaces, and let
--   $\Pi P=\{x:\ \langle u,x\rangle\le\operatorname{vol}_{n+m-1}(P\,|\,u^{\perp})\ \text{for all } u \text{ with } \|u\|=1\}$
--   be the projection body. Split every $x\in\mathbb{R}^{n+m}$ as $x=(x',x'')$ with $x'=(x_1,\dots,x_n)\in\mathbb{R}^n$ and $x''=(x_{n+1},\dots,x_{n+m})\in\mathbb{R}^m$.
--
--   For $k\in\mathbb{N}$ let $Z_k=\{y\in\mathbb{R}^k: |y_i|\le1 \text{ and } |y_i-y_j|\le1 \text{ for all } i,j\}$ be the centered Minkowski sum of the unit cube and the diagonal segment (the sum of $[0,1]^k$ and $\{t(1,\dots,1):0\le t\le1\}$, translated by $-(1,\dots,1)$), with support function $h_k(v)=\tfrac12\bigl(\sum_{i=1}^k|v_i|+|\sum_{i=1}^k v_i|\bigr)$.
--
--   **Theorem.** Let $P\subseteq\mathbb{R}^{n+m}$ be any set and let $c>0$. If
--   $\operatorname{vol}_{n+m-1}(P\,|\,u^{\perp})=c\,\bigl(h_n(u')+h_m(u'')\bigr)$
--   for every unit vector $u\in\mathbb{R}^{n+m}$, then
--
--   $$
--   \Pi P=c\,Z_n\times c\,Z_m=\bigl\{x\in\mathbb{R}^{n+m}:\ x'\in c\,Z_n\ \text{and}\ x''\in c\,Z_m\bigr\}.
--   $$
--
--   This is the two-block analogue of the identification of a projection body from a cube-plus-diagonal brightness formula. It is applied with $n=m=10$ and $c=1/(9!\,10!)$ to the product $T_{10}\times T_{10}$ of two corner simplices, whose brightness function has exactly this form, yielding $\Pi(T_{10}\times T_{10})=(Z_{10}\times Z_{10})/(9!\,10!)$, whose volume then enters the normalized projection-body ratio of the counterexample.
--
--   **Formalization Note** $P$ is an arbitrary subset of `E (n + m) = EuclideanSpace ℝ (Fin (n + m))`; no convexity, compactness or measurability is required, since the brightness formula is a hypothesis. The splitting $x\mapsto(x',x'')$ is `EuclideanSpace.finAddEquivProd`, the bound $h_n(u')+h_m(u'')$ is `blockSupport u`, and $c\,Z_n\times c\,Z_m$ is `DiagonalZonotope.euclideanProduct n m c`, the preimage under this splitting of the product of the two sets `DiagonalZonotope.euclidean c`. The projection volume is the real number (`toReal`) of `μHE[n + m - 1]` of the projected set, with natural-number subtraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductZonotopeBridge.lean#L27-L50

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
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductZonotopeBridge

open OAI OAI.ProjectionCounterexample
open Set
open scoped RealInnerProductSpace

theorem OAI.ProjectionCounterexample.projectionBody_eq_productZonotope {n m : ℕ} (P : Set (E (n + m)))
    (c : ℝ) (hc : 0 < c)
    (hbrightness : ∀ u : E (n + m), ‖u‖ = 1 → projectionVolume P u = c * blockSupport u) :
    projectionBody P = DiagonalZonotope.euclideanProduct n m c := by sorry
