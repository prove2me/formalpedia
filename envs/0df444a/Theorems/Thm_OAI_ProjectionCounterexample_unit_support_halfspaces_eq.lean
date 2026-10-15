-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_unit_support_halfspaces_eq
-- name    : OAI.ProjectionCounterexample.unit_support_halfspaces_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:01:01.886482+00:00
-- url     : https://prove2.me/theorems/638c2e30-14c7-4226-9acc-d5aa1f955d8a
-- title:
--   Unit directions suffice in halfspace descriptions with a positively homogeneous bound
-- statement:
--   Let $V$ be a real inner product space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, and let $f:V\to\mathbb{R}$ be a function with $f(0)\ge0$ that is positively homogeneous: $f(a u)=a\,f(u)$ for every real $a\ge0$ and every $u\in V$. Then the set of points satisfying the inequality $\langle u,x\rangle\le f(u)$ for all unit vectors $u$ coincides with the set of points satisfying it for all vectors $u$:
--
--   $$
--   \bigl\{x\in V:\ \langle u,x\rangle\le f(u)\ \text{for all } u\in V \text{ with } \|u\|=1\bigr\}
--   =\bigl\{x\in V:\ \langle u,x\rangle\le f(u)\ \text{for all } u\in V\bigr\}.
--   $$
--
--   Convex bodies are often defined by a family of support inequalities indexed by the unit sphere; the projection body, whose defining bound in direction $u$ is the volume of the shadow of a body on $u^{\perp}$, is the example of interest here. Explicit bodies such as zonotopes, on the other hand, are naturally described by inequalities $\langle u,x\rangle\le h(u)$ for all $u$, with $h$ their support function. For positively homogeneous bounds this lemma shows that the two descriptions define the same set, so that a brightness formula on the unit sphere can be matched directly with the halfspace description of an explicit zonotope.
--
--   **Formalization Note** No completeness or finite-dimensionality of $V$ is assumed. The hypothesis $f(0)\ge0$ is in fact implied by positive homogeneity (taking $a=0$ gives $f(0)=0$), but it is part of the statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/UnitSupport.lean#L11-L37

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

theorem OAI.ProjectionCounterexample.unit_support_halfspaces_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (hzero : 0 ≤ f 0)
    (hscale : ∀ (a : ℝ), 0 ≤ a → ∀ u, f (a • u) = a * f u) :
    {x : V | ∀ u, ‖u‖ = 1 → ⟪u, x⟫ ≤ f u} =
      {x : V | ∀ u, ⟪u, x⟫ ≤ f u} := by sorry
