-- Prove2me | Theorems.Thm_GlobalTheory_FiltrationMultiplicative_coeff_X_mul_part
-- name    : GlobalTheory.FiltrationMultiplicative.coeff_X_mul_part
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:52.706667+00:00
-- url     : https://prove2.me/theorems/b671f457-8892-456f-8a6c-abd5d8bb5c72
-- title:
--   Filtration Multiplicative: coeff X mul part
-- statement:
--   The Filtration Multiplicative construction uses the coeff X mul part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L103-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
variable {O : Type} [CommRing O] [IsLocalRing O]
open Classical

theorem GlobalTheory.FiltrationMultiplicative.coeff_X_mul_part {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) (m : Fin a →₀ ℕ) :
    coeff m (X i * part f i) = if IsFirst m i then coeff m f else 0 := by sorry
