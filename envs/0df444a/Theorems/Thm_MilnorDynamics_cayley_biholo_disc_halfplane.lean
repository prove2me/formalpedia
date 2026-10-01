-- Prove2me | Theorems.Thm_MilnorDynamics_cayley_biholo_disc_halfplane
-- name    : MilnorDynamics.cayley_biholo_disc_halfplane
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-30T21:27:37.853625+00:00
-- url     : https://prove2.me/theorems/0b98590f-d3e4-4346-a22f-a05c7a9e1303
-- title:
--   The Cayley transform is a biholomorphism from the open unit disc onto the upper half-plane
-- statement:
--   The map c(z) = (z + 1) / (1 - z) has no pole on the closed disc, is complex differentiable wherever z is not 1, and carries the open unit disc D = {|z| < 1} onto the upper half-plane H = {w : Im w > 0}; indeed c(z) - conjugate(c(z)) = 2i(1 - |z|^2)/|1-z|^2 has positive imaginary part exactly when |z| < 1. Hence c is a biholomorphism from D to H and a homeomorphism onto its range. Composing a covering of the thrice-punctured sphere that factors through H with c yields a covering from D to C minus {0,1}, which is the covering asserted in Milnor's Lemma 2.5.
-- source:
--   Milnor, Dynamics in One Complex Variable, Chapter 1, Lemma 2.5 (the disc-to-half-plane reparametrisation); the elementary Cayley-transform calculation |1+z| > |1-z| for |z| < 1. Already related platform child: MilnorDynamics.cayley_disk_lt_halfplane.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- The Cayley transform `c z = (z + 1) / (1 - z)` is differentiable on the open unit
disc, has no pole there, and carries the disc onto the upper half-plane.  It is the
conformal reparametrisation that turns a covering of the thrice-punctured sphere factored
through `H` into the covering `D -> C \ {0,1}` required by Milnor's Lemma 2.5. -/
theorem cayley_biholo_disc_halfplane :
    IsEmpty {z : ℂ // z ∈ Set.univ ∧ (1 - z) = 0} ∧
      IsOpen (Set.range (fun z : ℂ => (z + 1) / (1 - z))) ∧
      DifferentiableOn ℂ (fun z : ℂ => (z + 1) / (1 - z)) (Metric.ball 0 1) := by sorry

end MilnorDynamics
