-- Prove2me | Theorems.Thm_GlobalTheory_IdealPowerCoefficients_decomp
-- name    : GlobalTheory.IdealPowerCoefficients.decomp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:05:19.538086+00:00
-- url     : https://prove2.me/theorems/88ec891f-5635-4771-9c42-00df53b9f7e6
-- title:
--   Ideal Power Coefficients: decomp
-- statement:
--   The Ideal Power Coefficients construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L106-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L106-L131

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

theorem GlobalTheory.IdealPowerCoefficients.decomp [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R) :
    f = C (coeff 0 f) + ∑ k, X k * cof f k := by sorry
