-- Prove2me | Theorems.Thm_GlobalTheory_IdealPowerCoefficients_pick_mem
-- name    : GlobalTheory.IdealPowerCoefficients.pick_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:55.922195+00:00
-- url     : https://prove2.me/theorems/fa3bbaf2-6c12-4232-aa08-14d628573c7e
-- title:
--   Ideal Power Coefficients: pick mem
-- statement:
--   The Ideal Power Coefficients construction uses the pick mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L93-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IdealPowerCoefficients
open MvPowerSeries Finsupp
variable {R : Type u_1} [CommRing R] {κ : Type u_2}

theorem GlobalTheory.IdealPowerCoefficients.pick_mem (d : κ →₀ ℕ) (h : d ≠ 0) (k : κ) : pick d k ∈ d.support := by sorry
