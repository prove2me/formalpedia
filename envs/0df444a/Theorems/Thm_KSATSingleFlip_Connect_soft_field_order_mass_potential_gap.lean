-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_order_mass_potential_gap
-- name    : KSATSingleFlip.Connect.soft_field_order_mass_potential_gap
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:20:43.408212+00:00
-- url     : https://prove2.me/theorems/d80860e8-1d6e-4549-9ce5-84ddca5e0ffb
-- title:
--   Concave-test order controls the potential increment by the mass increment
-- statement:
--   If two finite soft-field measures are ordered by all continuous concave endpoint-zero tests, then the increment of the potential h is nonnegative and no larger than the increment of the total mass. The proof tests the order with g and f−g, as in the proof of Lemma 4.5. This does not assert preservation of the order by the Poisson update.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, proof of Lemma 4.5 and equation (4.9), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldOrder
import Mathlib
open MeasureTheory KSATSingleFlip.Connect Set
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_order_mass_potential_gap (ν' ν : Measure ℝ) [IsFiniteMeasure ν'] [IsFiniteMeasure ν]
    (hord : softFieldLE ν' ν) :
    0 ≤ hPot ν-hPot ν' ∧
      hPot ν-hPot ν' ≤ (massM ν).toReal-(massM ν').toReal := by sorry
