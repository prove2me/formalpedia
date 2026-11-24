-- Prove2me | Theorems.Thm_GlobalTheory_IdealPowerCoefficients_coeffIdeal_mul_le
-- name    : GlobalTheory.IdealPowerCoefficients.coeffIdeal_mul_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:05:15.065559+00:00
-- url     : https://prove2.me/theorems/de8a36f8-f878-48e1-8136-36deb4ce3313
-- title:
--   Ideal Power Coefficients: coeff Ideal mul le
-- statement:
--   The Ideal Power Coefficients construction uses the coeff Ideal mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L35-L49

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

theorem GlobalTheory.IdealPowerCoefficients.coeffIdeal_mul_le (I : Ideal R) (a b : ℕ) :
    coeffIdeal (κ := κ) I a * coeffIdeal I b ≤ coeffIdeal I (a + b) := by sorry
