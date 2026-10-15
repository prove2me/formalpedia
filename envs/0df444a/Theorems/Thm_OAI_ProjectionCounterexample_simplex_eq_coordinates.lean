-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_simplex_eq_coordinates
-- name    : OAI.ProjectionCounterexample.simplex_eq_coordinates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:40:49.88454+00:00
-- url     : https://prove2.me/theorems/8e7d487f-ff27-458b-8dde-a738abeb6b89
-- title:
--   Coordinate description of the standard simplex
-- statement:
--   For $d\in\mathbb{N}$ let $T_d=\operatorname{conv}\{0,e_1,\dots,e_d\}$ be the standard simplex in $d$-dimensional Euclidean space $\mathbb{R}^d$, the convex hull of the origin and the standard basis vectors $e_1,\dots,e_d$. Then $T_d$ is cut out by explicit linear inequalities:
--   $$
--   T_d=\Bigl\{x\in\mathbb{R}^d:\ x_i\ge 0\ \text{ for all } i,\ \ \sum_{i=1}^{d} x_i\le 1\Bigr\}.
--   $$
--
--   The identity holds for every $d$, including $d=0$, where both sides are the one-point space. It converts the convex-hull definition of the simplex into inequalities, which is the form in which its facets, its shadows and its volume are handled afterwards.
--
--   **Formalization Note** The ambient space is `EuclideanSpace ℝ (Fin d)`, so coordinates are indexed by `Fin d`, and `simplex d` is the convex hull of `0` together with the vectors `EuclideanSpace.single i 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ConvexGeometry.lean#L34-L79

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

open OAI OAI.ProjectionCounterexample
open Set

theorem OAI.ProjectionCounterexample.simplex_eq_coordinates (d : ℕ) :
    simplex d = {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by sorry
