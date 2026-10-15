-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_simplex_projectionVolume
-- name    : OAI.ProjectionCounterexample.simplex_projectionVolume
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:00:03.367697+00:00
-- url     : https://prove2.me/theorems/14bf8232-a3f8-4655-a86d-64e08a0a3403
-- title:
--   Projection volumes of the standard simplex: $\big(\sum_i|u_i|+|\sum_i u_i|\big)/(2\,n!)$
-- statement:
--   Index the coordinates of $\mathbb{R}^d$ by $\{0,\dots,d-1\}$ and let $e_0,\dots,e_{d-1}$ be the standard basis. For $d\ge1$ let
--   $$
--   T_d=\operatorname{conv}\{0,e_0,\dots,e_{d-1}\}\subset\mathbb{R}^{d}
--   $$
--   be the standard simplex. For a unit vector $u\in\mathbb{R}^{d}$ let $P_u$ be the orthogonal projection of $\mathbb{R}^d$ onto $u^\perp$, and define the projection volume of a set $P\subseteq\mathbb{R}^d$ in direction $u$ as
--   $$
--   \operatorname{pv}(P,u)=\mathcal H^{d-1}\big(P_u(P)\big),
--   $$
--   the $(d-1)$-dimensional Euclidean Hausdorff measure (normalized to agree with Lebesgue measure in dimension $d-1$) of its orthogonal shadow, taken as a real number.
--
--   **Theorem.** For every integer $n\ge1$ and every unit vector $u\in\mathbb{R}^{n+1}$,
--   $$
--   \operatorname{pv}(T_{n+1},u)=\frac{\sum_{i=0}^{n}|u_i|+\big|\sum_{i=0}^{n}u_i\big|}{2\,n!} .
--   $$
--
--   Equivalently, the numerator is the sum of $|\varphi(u)|$ over the $n+2$ outward facet functionals $\varphi(x)=-x_i$ ($0\le i\le n$) and $\varphi(x)=\sum_ix_i$ of the simplex. Since the projection body of $P$ is the set of $x$ with $\langle u,x\rangle\le\operatorname{pv}(P,u)$ for all unit vectors $u$, the formula describes the projection body of the simplex explicitly; the case $n=19$ concerns the simplex in $\mathbb{R}^{20}$ that appears in the dimension-$20$ comparison.
--
--   **Formalization Note** `projectionVolume P u` is `(μHE[d - 1] (project u '' P)).toReal` with `d = n + 1`, so $d-1=n$, and `simplex (n + 1)` is the convex hull of $0$ and the vectors `EuclideanSpace.single i 1`. The hypothesis `0 < n` is used to make distinct facets transverse; it excludes the one-dimensional simplex $T_1=[0,1]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/SimplexBrightness.lean#L75-L93

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
open Set MeasureTheory Measure
open scoped RealInnerProductSpace

theorem OAI.ProjectionCounterexample.simplex_projectionVolume {n : ℕ} (hn : 0 < n)
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    projectionVolume (simplex (n + 1)) u =
      ((∑ i, |u i|) + |∑ i, u i|) / (2 * (n.factorial : ℝ)) := by sorry
