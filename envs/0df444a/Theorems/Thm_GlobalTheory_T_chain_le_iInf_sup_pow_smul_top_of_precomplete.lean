-- Prove2me | Theorems.Thm_GlobalTheory_T_chain_le_iInf_sup_pow_smul_top_of_precomplete
-- name    : GlobalTheory.T.chain_le_iInf_sup_pow_smul_top_of_precomplete
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:31:02.936992+00:00
-- url     : https://prove2.me/theorems/ae28f149-51af-42f5-a33d-84ccc6b5b1a1
-- title:
--   T: chain le i Inf sup pow smul top of precomplete
-- statement:
--   The T construction uses the chain le i Inf sup pow smul top of precomplete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChainLeIInfSupPowSmulTopOfPrecompleteStatement.lean#L5-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChainLeIInfSupPowSmulTopOfPrecompleteStatement.lean#L5-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChainLeIInfSupPowSmulTopOfPrecomplete
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChainLeIInfSupPowSmulTopOfPrecompleteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.chain_le_iInf_sup_pow_smul_top_of_precomplete : ∀ (Λ : Type) [CommRing Λ] (I : Ideal Λ) [IsPrecomplete I Λ] (a : ℕ) (N : ℕ → Submodule Λ (Fin a → Λ)),
  (∀ n, N (n + 1) ≤ N n) → (∀ n, I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ N n) →
  (∀ n, N n ≤ N (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))) →
  ∀ n, N n ≤ (⨅ k, N k) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by sorry
