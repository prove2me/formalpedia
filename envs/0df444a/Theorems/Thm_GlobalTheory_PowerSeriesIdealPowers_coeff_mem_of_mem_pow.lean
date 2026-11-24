-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_coeff_mem_of_mem_pow
-- name    : GlobalTheory.PowerSeriesIdealPowers.coeff_mem_of_mem_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:33.262551+00:00
-- url     : https://prove2.me/theorems/2135c76e-8c26-4be3-858f-25dd7f68178e
-- title:
--   Power Series Ideal Powers: coeff mem of mem pow
-- statement:
--   The Power Series Ideal Powers construction uses the coeff mem of mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MemPowOfCoeffMem.lean#L18-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MemPowOfCoeffMem.lean#L18-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MemPowOfCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesIdealPowers
open MvPowerSeries IsLocalRing
variable {O : Type} [CommRing O] [IsLocalRing O]

theorem GlobalTheory.PowerSeriesIdealPowers.coeff_mem_of_mem_pow {σ : Type} (n : ℕ) :
    ∀ f ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n, ∀ d : σ →₀ ℕ,
      coeff d f ∈ (maximalIdeal O) ^ (n - d.degree) := by sorry
