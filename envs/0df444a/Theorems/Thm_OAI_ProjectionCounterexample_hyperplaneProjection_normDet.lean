-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_hyperplaneProjection_normDet
-- name    : OAI.ProjectionCounterexample.hyperplaneProjection_normDet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:53:44.077637+00:00
-- url     : https://prove2.me/theorems/e330d7a8-1644-41fb-a9d6-834d8a5ba3cb
-- title:
--   Orthogonal projection between hyperplanes scales area by $|\langle n,u\rangle|$
-- statement:
--   Let $V$ be a finite-dimensional real inner product space and let $n,u\in V$ be unit vectors, $\|n\|=\|u\|=1$. For $v\in V$ write $v^\perp=\{x\in V:\langle v,x\rangle=0\}$, and let $P_u:V\to V$ be the orthogonal projection onto $u^\perp$, $P_ux=x-\langle u,x\rangle u$. Consider the restriction of $P_u$ to the hyperplane $n^\perp$, as a linear map $P_u|_{n^\perp}:n^\perp\to V$. For a linear map $L$ out of a finite-dimensional inner product space, let $J(L)=\sqrt{\det(L^{*}L)}$ be its norm determinant, the factor by which $L$ scales volume of the dimension of its domain.
--
--   **Theorem.**
--   $$
--   J\big(P_u|_{n^\perp}\big)=|\langle n,u\rangle| .
--   $$
--
--   Geometrically, orthogonally projecting a piece of a hyperplane with unit normal $n$ onto the hyperplane $u^\perp$ multiplies its $(\dim V-1)$-dimensional area by $|\cos\angle(n,u)|$; when $n\perp u$ the projection is degenerate and the factor is $0$. This is the linear-algebra core of the facet-by-facet computation of projection volumes of polytopes.
--
--   **Formalization Note** The map is `hyperplaneProjection n u`, the composition of `(perpendicularTo u).starProjection` with the inclusion of the subspace `perpendicularTo n`, where `perpendicularTo v` is the orthogonal complement of the span of $v$. $J$ is Mathlib's `LinearMap.normDet`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/HyperplaneJacobian.lean#L49-L100

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

open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem OAI.ProjectionCounterexample.hyperplaneProjection_normDet {n u : V} (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) :
    (hyperplaneProjection n u).normDet = |⟪n, u⟫| := by sorry
