-- Prove2me | Theorems.Thm_NewtonGravitation_uniformShell_inner_mass_zero
-- name    : NewtonGravitation.uniformShell_inner_mass_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T18:58:13.487986+00:00
-- url     : https://prove2.me/theorems/efbf1739-f434-42cd-ae40-e5448b214456
-- title:
--   Uniform shell has no mass strictly inside its radius
-- statement:
--   The uniform shell is the pushforward of a surface measure supported on the unit sphere under the map u↦a•u. Every image point has norm exactly a for positive a, so the preimage of the open ball of radius a is empty. Consequently that open ball has shell measure zero. This supplies the inner-support hypothesis for the general hollow-shell theorem without relying on the gravitational field result.
-- source:
--   Prove2Me, Newton's Law of Universal Gravitation: the Shell Theorem, https://prove2.me/missions/Newton%27s_Law_of_Universal_Gravitation%3A_the_Shell_Theorem

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.uniformShell_inner_mass_zero (M : NNReal) (a : ℝ)
    (ha : 0 < a) : (uniformShell M a) (Metric.ball (0 : Space) a) = 0 := by sorry
