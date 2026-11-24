-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentSmallJumpCutoffSequenceV1
-- name    : Kyprianou.Ch03.momentSmallJumpCutoffSequenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T13:20:10.882611+00:00
-- url     : https://prove2.me/theorems/0b630e29-b804-4087-8dde-ea48713fc289
-- title:
--   Positive annular cutoff sequence tending to zero
-- statement:
--   Take e(n)=1/(n+2), using the real inverse limit at infinity.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; finite compensated small-jump approximation, reusing Chapter 8 finite transform construction and published compound-Poisson transform.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentSmallJumpCutoffSequenceV1
    :
    ∃ e : ℕ → Real, (∀ n, 0 < e n ∧ e n < 1) ∧ Tendsto e atTop (𝓝 0) := by sorry
