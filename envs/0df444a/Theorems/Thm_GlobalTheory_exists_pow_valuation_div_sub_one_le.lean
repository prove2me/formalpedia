-- Prove2me | Theorems.Thm_GlobalTheory_exists_pow_valuation_div_sub_one_le
-- name    : GlobalTheory.exists_pow_valuation_div_sub_one_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:25.9808+00:00
-- url     : https://prove2.me/theorems/47b930a8-533f-4f42-bc6f-c41a73e2b724
-- title:
--   Global Theory: exists pow valuation div sub one le
-- statement:
--   The Global Theory construction uses the exists pow valuation div sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsPowValuationDivSubOneLeOfCongr.lean#L6-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsPowValuationDivSubOneLeOfCongr.lean#L6-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsPowValuationDivSubOneLeOfCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.exists_pow_valuation_div_sub_one_le :
    ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), c ≠ 0 →
      ∀ n : ℕ, ∃ N : ℕ, ∀ k : 𝓞 E, k - c ∈ v.asIdeal ^ N →
        v.valuation E ((k : E) / (c : E) - 1) ≤ WithZero.exp (-(n : ℤ)) := by sorry
