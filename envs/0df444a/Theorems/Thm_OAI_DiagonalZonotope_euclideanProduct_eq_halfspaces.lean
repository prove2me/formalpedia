-- Prove2me | Theorems.Thm_OAI_DiagonalZonotope_euclideanProduct_eq_halfspaces
-- name    : OAI.DiagonalZonotope.euclideanProduct_eq_halfspaces
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:48:21.388086+00:00
-- url     : https://prove2.me/theorems/eb32ea22-dba3-4404-9427-7f2f13c90d48
-- title:
--   Halfspace description of a product of two dilated diagonal zonotopes
-- statement:
--   For $k\in\mathbb{N}$ let $Z_0^{(k)}\subseteq\mathbb{R}^k$ be the centered diagonal zonotope $\{x:\ x+\mathbf 1\in[0,1]^k+[0,1]\,\mathbf 1\}$, and for $v\in\mathbb{R}^k$ let
--   $$
--   h(v)=\frac12\Bigl(\sum_{i=1}^k|v_i|+\Bigl|\sum_{i=1}^k v_i\Bigr|\Bigr)
--   $$
--   be its support function. Let $n,m\in\mathbb{N}$ and $c>0$, and split the Euclidean space $\mathbb{R}^{n+m}=\mathbb{R}^n\times\mathbb{R}^m$, writing $x=(x',x'')$ with $x'$ the first $n$ and $x''$ the last $m$ coordinates. Then the product of the two dilates $c\,Z_0^{(n)}$ and $c\,Z_0^{(m)}$ is
--   $$
--   c\,Z_0^{(n)}\times c\,Z_0^{(m)}=\Bigl\{x\in\mathbb{R}^{n+m}:\ \langle u,x\rangle\le c\,\bigl(h(u')+h(u'')\bigr)\ \text{ for all } u=(u',u'')\in\mathbb{R}^{n+m}\Bigr\},
--   $$
--   where $\langle\cdot,\cdot\rangle$ is the standard inner product.
--
--   In other words, the support function of the product is the sum of the support functions of the two blocks. With $n=m=10$ and $c=1/(9!\,10!)$ this product is the projection body of $T_{10}\times T_{10}$, and the halfspace form is what allows it to be matched with the definition of the projection body.
--
--   **Formalization Note** The product is `euclideanProduct n m c`, the preimage under `EuclideanSpace.finAddEquivProd` of `euclidean c ×ˢ euclidean c`, where `euclidean c` is the dilate $c\,Z_0^{(k)}$ transported to `EuclideanSpace ℝ (Fin k)`; $h$ is `support` applied to the coordinate vectors of the two blocks of $u$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Product.lean#L47-L75

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

open OAI OAI.DiagonalZonotope
open Set
open scoped RealInnerProductSpace

theorem OAI.DiagonalZonotope.euclideanProduct_eq_halfspaces (n m : ℕ) (c : ℝ) (hc : 0 < c) :
    euclideanProduct n m c =
      {x | ∀ u : EuclideanSpace ℝ (Fin (n + m)), ⟪u, x⟫ ≤ c *
        (support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).1) +
         support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).2))} := by sorry
