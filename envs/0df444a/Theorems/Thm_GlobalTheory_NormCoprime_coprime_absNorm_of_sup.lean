-- Prove2me | Theorems.Thm_GlobalTheory_NormCoprime_coprime_absNorm_of_sup
-- name    : GlobalTheory.NormCoprime.coprime_absNorm_of_sup
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:34:32.664968+00:00
-- url     : https://prove2.me/theorems/319395d1-b24d-48bc-94d4-899d40703cdc
-- title:
--   Norm Coprime: coprime abs Norm of sup
-- statement:
--   The Norm Coprime construction uses the coprime abs Norm of sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoprimeIntegerInIdeal.lean#L6-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoprimeIntegerInIdeal.lean#L6-L29

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

theorem GlobalTheory.NormCoprime.coprime_absNorm_of_sup {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm I) p := by sorry
