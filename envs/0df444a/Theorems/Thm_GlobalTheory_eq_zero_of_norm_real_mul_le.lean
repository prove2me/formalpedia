-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_norm_real_mul_le
-- name    : GlobalTheory.eq_zero_of_norm_real_mul_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:02.918041+00:00
-- url     : https://prove2.me/theorems/1a63ee73-133d-4e9d-9e63-3ffec5ef4832
-- title:
--   Global Theory: eq zero of norm real mul le
-- statement:
--   The Global Theory construction uses the eq zero of norm real mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EntireAntilinearLatticePeriodsConst.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EntireAntilinearLatticePeriodsConst.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EntireAntilinearLatticePeriodsConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory

theorem GlobalTheory.eq_zero_of_norm_real_mul_le {c : ℂ} {C : ℝ} (h : ∀ r : ℝ, ‖(r : ℂ) * c‖ ≤ C) : c = 0 := by sorry
