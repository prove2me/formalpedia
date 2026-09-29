-- Prove2me | Theorems.Thm_JordanCurve_subtype_arc_is_schoenflies_arc
-- name    : JordanCurve.subtype_arc_is_schoenflies_arc
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T07:56:57.040196+00:00
-- url     : https://prove2.me/theorems/1eda9f0c-deaa-4ff1-bd35-5de6858bb85c
-- title:
--   Equivalence of the interval-subtype and set-level arc parametrizations
-- statement:
--   A continuous injective map $\alpha:[0,1]\to\mathbb R^2$ has an image that is a simple arc under the parametrization convention of the Schoenflies formalization. This bridges the two representations of the same embedded interval.
-- source:
--   https://github.com/alonamaloh/schoenflies-lean/blob/05a43d29cde026618777db3d4e4316204ccca237/Schoenflies/Curve.lean#L42-L43

import Definitions.Def_SchoenfliesCurveCore

namespace JordanCurve

/-- Convert an interval-subtype arc into the parametrized arc predicate
used by the Schoenflies formalization. -/
theorem subtype_arc_is_schoenflies_arc
    (α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (hα : Continuous α) (hinj : Function.Injective α) :
    Schoenflies.IsArc (Set.range α) := by sorry

end JordanCurve
