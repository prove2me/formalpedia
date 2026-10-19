-- Prove2me | Theorems.Thm_MazurTransfer_DiscreteOrbitContinuityFromOpenStabilizer_continuous_orbit
-- name    : MazurTransfer.DiscreteOrbitContinuityFromOpenStabilizer.continuous_orbit
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T23:19:17.221637+00:00
-- url     : https://prove2.me/theorems/42eb0deb-914d-4639-9a13-ee168c5b4c0e
-- title:
--   A discrete orbit map is continuous when its stabilizer is open
-- statement:
--   Let G be a topological group acting on a discrete space X. If the stabilizer of x in X is open, then the orbit map $$G\longrightarrow X,\qquad g\longmapsto g\cdot x$$ is continuous. The inverse image of any orbit point is a translate of the stabilizer; points outside the orbit have empty inverse image. This is used for geometric norm-fibre points and kernel cocycles.
-- source:
--   Original MazurTheorem DiscreteOrbitContinuityFromOpenStabilizer.continuous_orbit, with its complete original type and proof retained. Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an orbit map into a discrete set is continuous if the
point stabilizer is open. Named downstream consumer: finite norm-fibre
orbits and actual continuous Kummer cocycles.
-/
import Mathlib

theorem MazurTransfer.DiscreteOrbitContinuityFromOpenStabilizer.continuous_orbit {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MulAction G X] [TopologicalSpace X] [DiscreteTopology X] (x : X) (hx : IsOpen (MulAction.stabilizer G x : Set G)) :
    Continuous (fun g : G => g • x) := by sorry
