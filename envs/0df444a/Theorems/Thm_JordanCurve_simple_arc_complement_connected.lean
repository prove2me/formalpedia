-- Prove2me | Theorems.Thm_JordanCurve_simple_arc_complement_connected
-- name    : JordanCurve.simple_arc_complement_connected
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T00:26:43.925286+00:00
-- url     : https://prove2.me/theorems/b2172fe0-3a09-4324-a482-74fb1ed16298
-- title:
--   A simple arc does not separate the plane
-- statement:
--   For every continuous injective map $\alpha:[0,1]\to\mathbb R^2$, the complement $\mathbb R^2\setminus\alpha([0,1])$ is connected. This is the non-separation theorem for a planar simple arc, a key step in an elementary proof of Jordan separation.
-- source:
--   Schoenflies/JordanClosed.lean, arc-complement theorem and its use in the Jordan proof, https://github.com/alonamaloh/schoenflies-lean/blob/main/Schoenflies/JordanClosed.lean.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic

namespace JordanCurve
theorem simple_arc_complement_connected
    (α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (hα : Continuous α) (hinj : Function.Injective α) :
    IsConnected ((Set.range α)ᶜ) := by sorry
end JordanCurve
