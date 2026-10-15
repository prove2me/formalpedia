-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_volume_linear_level_eq_zero
-- name    : OAI.ProjectionCounterexample.volume_linear_level_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:58:57.292125+00:00
-- url     : https://prove2.me/theorems/8cee8b60-514c-4f78-9bb2-86d41710f8a3
-- title:
--   Level sets of a nonzero linear functional have Haar measure zero
-- statement:
--   Let $V$ be a finite-dimensional real normed vector space, equipped with its Borel $\sigma$-algebra and a measure $\mu$ that is an additive Haar measure (for example, Lebesgue measure on $\mathbb{R}^d$). Let $f:V\to\mathbb{R}$ be a nonzero linear functional and $c\in\mathbb{R}$.
--
--   **Theorem.**
--   $$
--   \mu\big(\{x\in V:\ f(x)=c\}\big)=0 .
--   $$
--
--   Every level set of a nonzero linear functional is an affine hyperplane, so the theorem says that affine hyperplanes are Haar-null. In the projection-volume computations it is used in the parameter space of a facet chart, to show that the part of a facet lying on another facet's hyperplane is negligible.
--
--   **Formalization Note** The measure is the `volume` of a `MeasureSpace V` structure with `[BorelSpace V]` and `[Measure.IsAddHaarMeasure volume]`; the functional is a linear map `f : V →ₗ[ℝ] ℝ` with `f ≠ 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/NullHyperplane.lean#L10-L29

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
open Set MeasureTheory

theorem OAI.ProjectionCounterexample.volume_linear_level_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
    [Measure.IsAddHaarMeasure (volume : Measure V)]
    (f : V →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) :
    volume {x : V | f x = c} = 0 := by sorry
