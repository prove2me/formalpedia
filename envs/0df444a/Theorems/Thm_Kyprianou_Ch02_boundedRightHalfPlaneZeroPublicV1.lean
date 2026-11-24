-- Prove2me | Theorems.Thm_Kyprianou_Ch02_boundedRightHalfPlaneZeroPublicV1
-- name    : Kyprianou.Ch02.boundedRightHalfPlaneZeroPublicV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:47:39.116629+00:00
-- url     : https://prove2.me/theorems/ed44b89d-12ad-48cb-9bda-bfb386abeccb
-- title:
--   Bounded right-half-plane holomorphic uniqueness
-- statement:
--   A bounded holomorphic function continuous up to the imaginary axis and vanishing there is zero in the closed right half-plane.
-- source:
--   Mathlib PhragmenLindelof.right_half_plane_of_bounded_on_real; Kyprianou (2006), Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

open Asymptotics Bornology
open scoped Asymptotics Filter Real

theorem Kyprianou.Ch02.boundedRightHalfPlaneZeroPublicV1 (f : ℂ → ℂ)
    (hd : DiffContOnCl ℂ f {z : ℂ | 0 < z.re})
    (M : ℝ) (hb : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ M)
    (hzero : ∀ x : ℝ, f ((x : ℂ) * Complex.I) = 0)
    (z : ℂ) (hz : 0 ≤ z.re) : f z = 0 := by sorry
