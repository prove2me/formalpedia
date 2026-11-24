-- Prove2me | Theorems.Thm_GlobalTheory_IdealPowerCoefficients_pick_eq
-- name    : GlobalTheory.IdealPowerCoefficients.pick_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:50.076804+00:00
-- url     : https://prove2.me/theorems/9230e80e-3ae6-48e8-b259-1983a7cbb57d
-- title:
--   Ideal Power Coefficients: pick eq
-- statement:
--   The Ideal Power Coefficients construction uses the pick eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L89-L91

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

theorem GlobalTheory.IdealPowerCoefficients.pick_eq (d : κ →₀ ℕ) (h : d ≠ 0) (k k' : κ) : pick d k = pick d k' := by sorry
