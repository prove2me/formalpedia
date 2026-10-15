-- Prove2me | Theorems.Thm_OAI_DiagonalZonotope_centered_support_le
-- name    : OAI.DiagonalZonotope.centered_support_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:46:11.670041+00:00
-- url     : https://prove2.me/theorems/5d23854e-5d39-4549-adc9-062ff16b36bd
-- title:
--   Support-function bound for the centered diagonal zonotope
-- statement:
--   Let $\iota$ be a finite index set and work in $\mathbb{R}^\iota$, with all-ones vector $\mathbf 1$. The diagonal zonotope is the Minkowski sum of the unit cube $Q=[0,1]^\iota$ and the diagonal segment from $0$ to $\mathbf 1$,
--   $$
--   Z=\{\,q+t\,\mathbf 1:\ q\in Q,\ t\in[0,1]\,\},
--   $$
--   and its centered translate is $Z_0=Z-\mathbf 1=\{x:\ x+\mathbf 1\in Z\}$, which is symmetric about the origin. For $u\in\mathbb{R}^\iota$ write
--   $$
--   h(u)=\frac12\Bigl(\sum_{i\in\iota}|u_i|+\Bigl|\sum_{i\in\iota}u_i\Bigr|\Bigr).
--   $$
--   Then for every direction $u\in\mathbb{R}^\iota$ and every point $x\in Z_0$,
--   $$
--   \sum_{i\in\iota}u_i\,x_i\ \le\ \frac12\Bigl(\sum_{i\in\iota}|u_i|+\Bigl|\sum_{i\in\iota}u_i\Bigr|\Bigr)=h(u).
--   $$
--
--   Since $Z_0=\sum_i[-\tfrac12e_i,\tfrac12e_i]+[-\tfrac12\mathbf 1,\tfrac12\mathbf 1]$ is a sum of segments, $h$ is its support function; the inequality above is the "every point satisfies every support inequality" half of that statement, and the converse (that these halfspaces cut out exactly $Z_0$) is proved separately. For $\iota=\{1,\dots,d\}$ with $d\ge 2$ and a unit vector $u$, $h(u)/(d-1)!$ is the volume of the orthogonal projection of the simplex $T_d$ onto $u^\perp$, which is why this zonotope appears as a projection body.
--
--   **Formalization Note** $Z_0$ is `centered` in `ι → ℝ` under `[Fintype ι]`, and the pairing is written as the coordinate sum $\sum_i u_ix_i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Support.lean#L67-L82

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

theorem OAI.DiagonalZonotope.centered_support_le (u x : ι → ℝ) (hx : x ∈ centered) :
    (∑ i, u i * x i) ≤ ((∑ i, |u i|) + |∑ i, u i|) / 2 := by sorry
