-- Prove2me | Theorems.Thm_NewtonGravitation_uniformShell_geometry
-- name    : NewtonGravitation.uniformShell_geometry
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T11:58:16.489114+00:00
-- url     : https://prove2.me/theorems/2a057491-db57-4035-b07e-706aa0b94b2b
-- title:
--   Uniform spherical-shell measure: finite mass, rotational invariance and inner support
-- statement:
--   Let $\sigma_{M,a}$ be the uniform spherical-shell measure defined in Newton's gravitation mission, with mass $M\ge 0$ and positive radius $a$. This measure is finite and invariant under every linear isometry fixing the origin. It assigns zero mass to the open ball strictly inside its radius:
--
--   $$\sigma_{M,a}(\{y:\|y\|<a\})=0.$$
--
--   These geometric measure properties supply the hypotheses needed to apply the general interior shell theorem to a uniform hollow sphere. The finite-mass assertion also makes the shell a legitimate integrator for the gravitational field.
-- source:
--   Prove2Me, Newton's Law of Universal Gravitation: the Shell Theorem, Setting and Formalization scope, https://prove2.me/missions/Newton%27s_Law_of_Universal_Gravitation%3A_the_Shell_Theorem

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.uniformShell_geometry (M : NNReal) (a : ℝ) (ha : 0 < a) :
    IsFiniteMeasure (uniformShell M a) ∧
      IsSphericallySymmetric (uniformShell M a) ∧
      (uniformShell M a) (Metric.ball (0 : Space) a) = 0 := by sorry
