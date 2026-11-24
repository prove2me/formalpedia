-- Prove2me | Theorems.Thm_GlobalTheory_NormCoprime_exists_coprime_mem
-- name    : GlobalTheory.NormCoprime.exists_coprime_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:34:10.163277+00:00
-- url     : https://prove2.me/theorems/0e6b83b5-0b95-4151-b529-115f8a42f738
-- title:
--   Norm Coprime: exists coprime mem
-- statement:
--   The Norm Coprime construction uses the exists coprime mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoprimeIntegerInIdeal.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoprimeIntegerInIdeal.lean#L31-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoprimeIntegerInIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormCoprime

theorem GlobalTheory.NormCoprime.exists_coprime_mem : ∀ (K : Type) [Field K] [NumberField K] (c : Ideal (𝓞 K)) (l : ℕ), l.Prime → c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ c → (l : 𝓞 K) ∉ v.asIdeal) → ∃ m : ℕ, m.Coprime l ∧ (m : 𝓞 K) ∈ c := by sorry
