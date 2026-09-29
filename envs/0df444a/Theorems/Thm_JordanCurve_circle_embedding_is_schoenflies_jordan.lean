-- Prove2me | Theorems.Thm_JordanCurve_circle_embedding_is_schoenflies_jordan
-- name    : JordanCurve.circle_embedding_is_schoenflies_jordan
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T13:12:01.480524+00:00
-- url     : https://prove2.me/theorems/8ba8d97d-bcf2-438e-b5d8-dc864f3f1c64
-- title:
--   Unit-circle embeddings admit Jordan loop parameterizations
-- statement:
--   Every continuous injective map from the Euclidean unit circle into the plane has an image that can be parameterized by a continuous loop on [0,1] that is injective on [0,1). One may use the complex exponential map around the circle, together with the isometry between the complex plane and Euclidean two-space.
-- source:
--   https://github.com/alonamaloh/schoenflies-lean/tree/05a43d29cde026618777db3d4e4316204ccca237/Schoenflies; standard circle parameterization by complex exponential

import Definitions.Def_Schoenflies_Jordan
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace JordanCurve

/-- A continuous injective image of the unit circle is a Jordan curve in the interval-parametrized sense. -/
theorem circle_embedding_is_schoenflies_jordan
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    Schoenflies.IsJordanCurve (Set.range γ) := by sorry

end JordanCurve
