-- Prove2me | Theorems.Thm_GlobalTheory_mem_ideal_smul_top_pi_fin_iff
-- name    : GlobalTheory.mem_ideal_smul_top_pi_fin_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:23.155061+00:00
-- url     : https://prove2.me/theorems/25171d44-4bc4-4cd8-bf1c-a16ea0bf1fd1
-- title:
--   Global Theory: mem ideal smul top pi fin iff
-- statement:
--   The Global Theory construction uses the mem ideal smul top pi fin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChainLeIInfSupPowSmulTopOfPrecomplete.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChainLeIInfSupPowSmulTopOfPrecomplete.lean#L5-L16

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

theorem GlobalTheory.mem_ideal_smul_top_pi_fin_iff {Λ : Type} [CommRing Λ] (J : Ideal Λ) {a : ℕ}
    (y : Fin a → Λ) : y ∈ J • (⊤ : Submodule Λ (Fin a → Λ)) ↔ ∀ i, y i ∈ J := by sorry
