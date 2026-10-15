-- Prove2me | Theorems.Thm_OAI_DiagonalZonotope_scaled_centered_eq_support_halfspaces
-- name    : OAI.DiagonalZonotope.scaled_centered_eq_support_halfspaces
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:47:14.678771+00:00
-- url     : https://prove2.me/theorems/cf254dab-580a-4ebc-ac1d-b5ec237b990b
-- title:
--   Halfspace description of a positive dilate of the centered diagonal zonotope
-- statement:
--   Let $\iota$ be a finite index set and work in $\mathbb{R}^\iota$, with all-ones vector $\mathbf 1$. The diagonal zonotope is the Minkowski sum of the unit cube $Q=[0,1]^\iota$ and the diagonal segment from $0$ to $\mathbf 1$,
--   $$
--   Z=\{\,q+t\,\mathbf 1:\ q\in Q,\ t\in[0,1]\,\},
--   $$
--   and its centered translate is $Z_0=Z-\mathbf 1=\{x:\ x+\mathbf 1\in Z\}$, which is symmetric about the origin. For $u\in\mathbb{R}^\iota$ write
--   $$
--   h(u)=\frac12\Bigl(\sum_{i\in\iota}|u_i|+\Bigl|\sum_{i\in\iota}u_i\Bigr|\Bigr).
--   $$
--   Then for every real $c>0$ the dilate $c\,Z_0=\{c\,y:\ y\in Z_0\}$ is
--   $$
--   c\,Z_0=\Bigl\{x\in\mathbb{R}^\iota:\ \sum_{i\in\iota}u_i\,x_i\le c\,h(u)\ \text{ for all } u\in\mathbb{R}^\iota\Bigr\}.
--   $$
--
--   So $c\,h$ is the support function of $c\,Z_0$ and the dilate is the intersection of the corresponding halfspaces. In the counterexample, the projection body of the simplex $T_{20}$ is the dilate with $c=1/19!$, and products of two dilates with $c=1/(9!\,10!)$ describe the projection body of $T_{10}\times T_{10}$.
--
--   **Formalization Note** The dilate is the image `(fun y => c • y) '' centered` in `ι → ℝ`; the statement assumes `[Fintype ι]`, `[DecidableEq ι]` and `0 < c`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Scaling.lean#L29-L48

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem OAI.DiagonalZonotope.scaled_centered_eq_support_halfspaces (c : ℝ) (hc : 0 < c) :
    (fun y : ι → ℝ => c • y) '' centered =
      {x | ∀ u : ι → ℝ, (∑ i, u i * x i) ≤
        c * (((∑ i, |u i|) + |∑ i, u i|) / 2)} := by sorry
