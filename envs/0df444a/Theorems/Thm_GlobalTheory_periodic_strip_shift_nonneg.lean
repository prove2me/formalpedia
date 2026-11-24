-- Prove2me | Theorems.Thm_GlobalTheory_periodic_strip_shift_nonneg
-- name    : GlobalTheory.periodic_strip_shift_nonneg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:21.637821+00:00
-- url     : https://prove2.me/theorems/22db0922-0fcb-45a1-b5de-e25e177c5467
-- title:
--   Global Theory: periodic strip shift nonneg
-- statement:
--   The Global Theory construction uses the periodic strip shift nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodicLeftHalfPlaneShiftNonnegOfImPos.lean#L7-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodicLeftHalfPlaneShiftNonnegOfImPos.lean#L7-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodicLeftHalfPlaneShiftNonnegOfImPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
open GlobalTheory

theorem GlobalTheory.periodic_strip_shift_nonneg (c : ℝ) (f : ℂ → ℂ) (m : ℤ)
    (hf : DifferentiableOn ℂ f {s : ℂ | s.re < c})
    (hper : ∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m)
    (hpos : ∀ s : ℂ, s.re < c → 0 < (f s).im) : 0 ≤ m := by sorry
