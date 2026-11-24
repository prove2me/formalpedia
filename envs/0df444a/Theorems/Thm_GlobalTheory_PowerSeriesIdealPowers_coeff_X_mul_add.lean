-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_coeff_X_mul_add
-- name    : GlobalTheory.PowerSeriesIdealPowers.coeff_X_mul_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:34.106199+00:00
-- url     : https://prove2.me/theorems/d5162e04-ca6a-46e7-8efa-2057a145e7b2
-- title:
--   Power Series Ideal Powers: coeff X mul add
-- statement:
--   The Power Series Ideal Powers construction uses the coeff X mul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MemPowOfCoeffMem.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MemPowOfCoeffMem.lean#L45-L48

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

theorem GlobalTheory.PowerSeriesIdealPowers.coeff_X_mul_add {σ : Type} [DecidableEq σ] (i : σ) (g : MvPowerSeries σ O) (d : σ →₀ ℕ) :
    coeff (d + Finsupp.single i 1) (X i * g) = coeff d g := by sorry
