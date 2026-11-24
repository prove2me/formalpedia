-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_coprime_integer_in_ideal
-- name    : GlobalTheory.T.exists_coprime_integer_in_ideal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:33:46.12467+00:00
-- url     : https://prove2.me/theorems/f6716cb1-dd61-42ca-8ff0-0155842240df
-- title:
--   T: exists coprime integer in ideal
-- statement:
--   The T construction uses the exists coprime integer in ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoprimeIntegerInIdealStatement.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoprimeIntegerInIdealStatement.lean#L6-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoprimeIntegerInIdeal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoprimeIntegerInIdealStatement
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

theorem GlobalTheory.T.exists_coprime_integer_in_ideal : ∀ (K : Type) [Field K] [NumberField K] (c : Ideal (𝓞 K)) (l : ℕ), l.Prime → c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ c → (l : 𝓞 K) ∉ v.asIdeal) → ∃ m : ℕ, m.Coprime l ∧ (m : 𝓞 K) ∈ c := by sorry
