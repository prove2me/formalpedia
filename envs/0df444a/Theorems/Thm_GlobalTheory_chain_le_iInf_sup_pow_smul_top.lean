-- Prove2me | Theorems.Thm_GlobalTheory_chain_le_iInf_sup_pow_smul_top
-- name    : GlobalTheory.chain_le_iInf_sup_pow_smul_top
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:34.940806+00:00
-- url     : https://prove2.me/theorems/0c37e77f-e804-4e31-a511-9072761ec5cf
-- title:
--   Global Theory: chain le i Inf sup pow smul top
-- statement:
--   The Global Theory construction uses the chain le i Inf sup pow smul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChainLeIInfSupPowSmulTopOfPrecomplete.lean#L18-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChainLeIInfSupPowSmulTopOfPrecomplete.lean#L18-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChainLeIInfSupPowSmulTopOfPrecomplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.chain_le_iInf_sup_pow_smul_top :
    ∀ (Λ : Type) [CommRing Λ] (I : Ideal Λ) [IsPrecomplete I Λ] (a : ℕ)
      (N : ℕ → Submodule Λ (Fin a → Λ)),
  (∀ n, N (n + 1) ≤ N n) → (∀ n, I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ N n) →
  (∀ n, N n ≤ N (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))) →
  ∀ n, N n ≤ (⨅ k, N k) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by sorry
