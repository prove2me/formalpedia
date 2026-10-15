-- Prove2me | Theorems.Thm_OAI_DiagonalZonotope_mem_centered_iff
-- name    : OAI.DiagonalZonotope.mem_centered_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:45:57.527184+00:00
-- url     : https://prove2.me/theorems/cd41ca72-f1f8-4c72-b58a-4136f906a5e9
-- title:
--   Inequality description of the centered diagonal zonotope
-- statement:
--   Let $\iota$ be a finite index set and work in $\mathbb{R}^\iota$, with all-ones vector $\mathbf 1$. The diagonal zonotope is the Minkowski sum of the unit cube $Q=[0,1]^\iota$ and the diagonal segment from $0$ to $\mathbf 1$,
--   $$
--   Z=\{\,q+t\,\mathbf 1:\ q\in Q,\ t\in[0,1]\,\},
--   $$
--   and its centered translate is $Z_0=Z-\mathbf 1=\{x:\ x+\mathbf 1\in Z\}$, which is symmetric about the origin. For every $x\in\mathbb{R}^\iota$,
--   $$
--   x\in Z_0\iff |x_i|\le 1\ \text{ for all } i\in\iota\quad\text{and}\quad |x_i-x_j|\le 1\ \text{ for all } i,j\in\iota .
--   $$
--
--   So $Z_0$ is the polytope cut out by the coordinate slabs $-1\le x_i\le 1$ and the difference slabs $-1\le x_i-x_j\le 1$. This finite description is the starting point for identifying $Z_0$ with the intersection of all halfspaces given by its support function.
--
--   **Formalization Note** $Z_0$ is `centered`, defined as $\{x\mid (j\mapsto x_j+1)\in Z\}$ in `ι → ℝ`, under `[Fintype ι]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Support.lean#L17-L51

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

open OAI OAI.DiagonalZonotope
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem OAI.DiagonalZonotope.mem_centered_iff (x : ι → ℝ) :
    x ∈ centered ↔ (∀ i, |x i| ≤ 1) ∧ ∀ i j, |x i - x j| ≤ 1 := by sorry
