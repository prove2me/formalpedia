-- Prove2me | Theorems.Thm_GlobalTheory_FiltrationMultiplicative_decomp
-- name    : GlobalTheory.FiltrationMultiplicative.decomp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:33.975807+00:00
-- url     : https://prove2.me/theorems/eb8581f7-f49c-4b02-9463-b000bdb1ba7b
-- title:
--   Filtration Multiplicative: decomp
-- statement:
--   The Filtration Multiplicative construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L114-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L114-L130

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

theorem GlobalTheory.FiltrationMultiplicative.decomp {a : ℕ} (f : MvPowerSeries (Fin a) O) :
    f = C (coeff 0 f) + ∑ i, X i * part f i := by sorry
