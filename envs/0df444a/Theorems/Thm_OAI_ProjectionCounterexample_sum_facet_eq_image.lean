-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_sum_facet_eq_image
-- name    : OAI.ProjectionCounterexample.sum_facet_eq_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:44:20.942452+00:00
-- url     : https://prove2.me/theorems/cbee0e56-a456-4ddd-a78b-3cb7fc8b6907
-- title:
--   The slanted facet of the simplex is an affine image of the lower-dimensional simplex
-- statement:
--   Let $n\in\mathbb{N}$ and let $T_m=\operatorname{conv}\{0,e_1,\dots,e_m\}\subseteq\mathbb{R}^m$ denote the standard simplex. Define the affine map $\sigma_n:\mathbb{R}^n\to\mathbb{R}^{n+1}$ by appending the coordinate that completes the sum to $1$:
--   $$
--   \sigma_n(y_1,\dots,y_n)=\Bigl(y_1,\dots,y_n,\ 1-\sum_{j=1}^n y_j\Bigr).
--   $$
--   Then the facet of $T_{n+1}$ opposite the origin is the image of $T_n$ under $\sigma_n$:
--   $$
--   \Bigl\{x\in T_{n+1}:\ \sum_{j=1}^{n+1}x_j=1\Bigr\}=\sigma_n(T_n).
--   $$
--
--   Together with the description of the coordinate facets as isometric images of $T_n$, this gives an explicit affine parametrization of every facet of $T_{n+1}$ by $T_n$. Unlike the coordinate charts, $\sigma_n$ is not an isometry: it is the graph of the linear function $y\mapsto -\sum_j y_j$ shifted by $e_{n+1}$, so measures on this facet pick up the Jacobian factor of a graph chart.
--
--   **Formalization Note** The map $\sigma_n$ is `sumFacetMap n`, written with `Fin.snoc`; coordinates of $\mathbb{R}^{n+1}$ are indexed by `Fin (n + 1)`, with the appended one at `Fin.last n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/FacetCoordinates.lean#L76-L102

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

open OAI OAI.ProjectionCounterexample
open Set

theorem OAI.ProjectionCounterexample.sum_facet_eq_image (n : ℕ) :
    {x ∈ simplex (n + 1) | ∑ j, x j = 1} = sumFacetMap n '' simplex n := by sorry
