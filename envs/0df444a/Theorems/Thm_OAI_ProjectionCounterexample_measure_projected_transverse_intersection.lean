-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_measure_projected_transverse_intersection
-- name    : OAI.ProjectionCounterexample.measure_projected_transverse_intersection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:59:12.995115+00:00
-- url     : https://prove2.me/theorems/c3bf6028-5252-4b0b-a8ec-23d2417c95ae
-- title:
--   Projected transverse sections of an affine chart are null for the chart-dimensional Hausdorff measure
-- statement:
--   Let $U$ be a finite-dimensional real inner product space of dimension $m$ and $V$ a real inner product space (not necessarily finite-dimensional), both carrying their Borel $\sigma$-algebras. On $V$ let $\mathcal H^m$ denote the $m$-dimensional Euclidean Hausdorff measure, i.e. the $m$-dimensional Hausdorff measure normalized so that it coincides with Lebesgue measure on $m$-dimensional Euclidean space. Let $L:U\to V$ and $q:V\to V$ be linear maps, $c\in V$, $g:V\to\mathbb{R}$ a linear functional, $r\in\mathbb{R}$, and $S,T\subseteq V$. Assume:
--
--   1. $S\subseteq c+L(U)$, i.e. $S$ lies in the affine plane parametrized by the chart $x\mapsto c+Lx$;
--   2. $T\subseteq\{y\in V:\ g(y)=r\}$;
--   3. $g\circ L\ne0$, i.e. $g$ is not constant on the plane $c+L(U)$, so the hyperplane $\{g=r\}$ is transverse to the chart.
--
--   **Theorem.** Under these assumptions
--   $$
--   \mathcal H^{m}\big(q(S\cap T)\big)=0,\qquad m=\dim U .
--   $$
--
--   In the projection-volume formula for polytopes, $S$ is a facet given by an $m$-dimensional affine chart and $T$ is another facet lying in a different supporting hyperplane. The theorem shows that the image of their intersection under any linear map, in particular under an orthogonal projection, is negligible for the facet-dimensional measure, so overlaps between projected facets do not affect sums of facet measures.
--
--   **Formalization Note** $\mathcal H^m$ is Mathlib's `euclideanHausdorffMeasure` (notation `μHE[m]`) with $m$ = `Module.finrank ℝ U`, and $q(S\cap T)$ is the image `q '' (S ∩ T)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/AffineChartMeasure.lean#L31-L50

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

open OAI OAI.ProjectionCounterexample
open Set MeasureTheory Measure
variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem OAI.ProjectionCounterexample.measure_projected_transverse_intersection (L : U →ₗ[ℝ] V) (c : V)
    (q : V →ₗ[ℝ] V) (g : V →ₗ[ℝ] ℝ) (r : ℝ) (S T : Set V)
    (hS : S ⊆ (fun x => c + L x) '' (univ : Set U))
    (hT : T ⊆ {y | g y = r}) (hg : g.comp L ≠ 0) :
    μHE[Module.finrank ℝ U] (q '' (S ∩ T)) = 0 := by sorry
