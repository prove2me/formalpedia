-- Prove2me | Theorems.Thm_NewtonGravitation_uniformShell_totalMass_support
-- name    : NewtonGravitation.uniformShell_totalMass_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T12:16:46.873994+00:00
-- url     : https://prove2.me/theorems/3cfbb37f-fd6f-4397-aad8-85c5d4802680
-- title:
--   Uniform spherical shell total mass and support at its radius
-- statement:
--   For the uniform spherical-shell measure of radius a>0 and nonnegative total mass M, the total real measure of Euclidean space equals M, and the measure assigns zero mass to the complement of the closed ball of radius a. The second assertion follows from the fact that the pushforward of unit-sphere surface measure under scaling by a lies on the sphere of radius a. The first is obtained by the normalisation in the definition of uniformShell. These exact measure identities are needed to reduce the exterior shell field to the general exterior shell theorem.
-- source:
--   Prove2Me Newton's Law of Universal Gravitation: the Shell Theorem, uniformShell definition and exterior shell milestone, https://prove2.me/missions/Newton%27s_Law_of_Universal_Gravitation%3A_the_Shell_Theorem

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.uniformShell_totalMass_support (M : NNReal) (a : ℝ) (ha : 0 < a) :
    (uniformShell M a).real Set.univ = (M : ℝ) ∧
      (uniformShell M a) (Metric.closedBall (0 : Space) a)ᶜ = 0 := by sorry
