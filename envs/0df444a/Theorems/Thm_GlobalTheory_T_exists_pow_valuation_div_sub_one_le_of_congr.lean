-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_pow_valuation_div_sub_one_le_of_congr
-- name    : GlobalTheory.T.exists_pow_valuation_div_sub_one_le_of_congr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:33.126451+00:00
-- url     : https://prove2.me/theorems/38c31568-aa05-4bbb-9049-a9cae3a06fc0
-- title:
--   T: exists pow valuation div sub one le of congr
-- statement:
--   The T construction uses the exists pow valuation div sub one le of congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsPowValuationDivSubOneLeOfCongrStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsPowValuationDivSubOneLeOfCongrStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsPowValuationDivSubOneLeOfCongr
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsPowValuationDivSubOneLeOfCongrStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_pow_valuation_div_sub_one_le_of_congr : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), c ≠ 0 → ∀ n : ℕ, ∃ N : ℕ, ∀ k : 𝓞 E, k - c ∈ v.asIdeal ^ N → v.valuation E ((k : E) / (c : E) - 1) ≤ WithZero.exp (-(n : ℤ)) := by sorry
