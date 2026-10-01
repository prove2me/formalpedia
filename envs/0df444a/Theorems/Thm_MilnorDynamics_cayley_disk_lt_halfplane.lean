-- Prove2me | Theorems.Thm_MilnorDynamics_cayley_disk_lt_halfplane
-- name    : MilnorDynamics.cayley_disk_lt_halfplane
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:38:51.757098+00:00
-- url     : https://prove2.me/theorems/a5dd6f7c-33ea-4558-b1c5-fa4e5658164e
-- title:
--   The Cayley transform sends the open unit disc into the open right half-plane
-- statement:
--   Let D be the open unit disc in the complex plane and let w(z) = (z+1)/(1-z) be the Cayley transform. Then w carries D bijectively onto the open right half-plane {w : C | 0 < w.re}; the inequality |1+z| > |1-z| for |z| < 1 is exactly the statement Re w > 0. This is the elementary geometric fact underlying the explicit universal cover of the twice-punctured plane in Milnor's Lemma 2.5.
-- source:
--   Milnor, Dynamics in One Complex Variable, Chapter 1, Lemma 2.5 setup (Cayley transform from the disc to the half-plane); the inequality |1+z| > |1-z| for |z| < 1.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open Complex

namespace MilnorDynamics

theorem cayley_disk_lt_halfplane (z : ℂ) (hz : z ∈ Metric.ball 0 1) :
    0 < ((z + 1) / (1 - z)).re := by sorry

end MilnorDynamics
