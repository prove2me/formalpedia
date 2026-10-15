-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_normDet_project_comp
-- name    : OAI.ProjectionCounterexample.normDet_project_comp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:54:42.327856+00:00
-- url     : https://prove2.me/theorems/91a2d4a9-70ca-415e-9c1a-f7e7d3f583fe
-- title:
--   Projecting a linear chart that lies in a hyperplane multiplies its area factor by $|\langle n,u\rangle|$
-- statement:
--   Let $U$ and $V$ be finite-dimensional real inner product spaces, $L:U\to V$ a linear map, and $n,u\in V$ unit vectors, $\|n\|=\|u\|=1$. Let $P_u:V\to V$ be the orthogonal projection onto $u^\perp=\{x\in V:\langle u,x\rangle=0\}$, and for a linear map $A$ out of $U$ let $J(A)=\sqrt{\det(A^{*}A)}$ be its norm determinant, the factor by which $A$ scales $(\dim U)$-dimensional volume. Assume that $L$ takes values in the hyperplane $n^\perp$ and that $U$ has the dimension of that hyperplane:
--   $$
--   \langle n,Lx\rangle=0\ \text{ for all }x\in U,\qquad \dim U=\dim V-1 .
--   $$
--
--   **Theorem.** Under these assumptions
--   $$
--   J(P_u\circ L)=|\langle n,u\rangle|\;J(L).
--   $$
--
--   The map $L$ is not required to be injective; if it is not, both sides vanish. The result says that a linear parametrization of a region in a hyperplane with unit normal $n$ has its area factor multiplied by $|\langle n,u\rangle|$ after orthogonal projection onto $u^\perp$. It is the form in which the hyperplane projection formula is applied to explicit facet charts, such as graph charts of simplex facets.
--
--   **Formalization Note** $P_u$ is `(perpendicularTo u).starProjection` regarded as a linear map, and $J$ is Mathlib's `LinearMap.normDet`. The dimension hypothesis is `Module.finrank ℝ U = Module.finrank ℝ V - 1` with natural-number subtraction; no truncation occurs because $V$ contains a unit vector.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/HyperplaneJacobian.lean#L102-L124

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

theorem OAI.ProjectionCounterexample.normDet_project_comp {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] (L : U →ₗ[ℝ] V) {n u : V}
    (hn : ‖n‖ = 1) (hu : ‖u‖ = 1)
    (hmem : ∀ x, ⟪n, L x⟫ = 0)
    (hrank : Module.finrank ℝ U = Module.finrank ℝ V - 1) :
    ((perpendicularTo u).starProjection.toLinearMap.comp L).normDet =
      |⟪n, u⟫| * L.normDet := by sorry
