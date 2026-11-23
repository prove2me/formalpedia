-- Prove2me | Theorems.Thm_GlobalTheory_IdealPowerCoefficients_coeff_cof
-- name    : GlobalTheory.IdealPowerCoefficients.coeff_cof
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:33.805285+00:00
-- url     : https://prove2.me/theorems/86b5f5c5-ea48-4606-a46b-ec421ab4bd4d
-- title:
--   Ideal Power Coefficients: coeff cof
-- statement:
--   The Ideal Power Coefficients construction uses the coeff cof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L101-L104

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

theorem GlobalTheory.IdealPowerCoefficients.coeff_cof [DecidableEq κ] (f : MvPowerSeries κ R) (k : κ) (e : κ →₀ ℕ) :
    coeff e (cof f k) = if pick (e + single k 1) k = k then coeff (e + single k 1) f else 0 := by sorry
