-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_update_symmetric
-- name    : KSATSingleFlip.Connect.soft_field_update_symmetric
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:54:49.2492+00:00
-- url     : https://prove2.me/theorems/3259e17f-a0a8-4bd2-aaef-73ebd2f008b0
-- title:
--   Soft-field update is symmetric
-- statement:
--   For a finite soft-field measure whose w-weighted jump intensity is finite, the soft-field update Rβν is invariant under negation. The symmetry follows from the law of the difference of two independent compound Poisson sums.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_update_symmetric (ν : Measure ℝ) [IsFiniteMeasure ν] (β : ℝ)
    (hfin : (ν.withDensity fun z => ENNReal.ofReal (wInt z)) Set.univ ≠ ∞) :
    Measure.map (fun z : ℝ => -z) (Rbeta β ν) = Rbeta β ν := by sorry
