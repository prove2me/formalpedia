-- Prove2me | Theorems.Thm_GlobalTheory_pairing_surjective_of_separating
-- name    : GlobalTheory.pairing_surjective_of_separating
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:13.697558+00:00
-- url     : https://prove2.me/theorems/0fff6c0c-eecc-441b-a9ac-9fecaf08f6e1
-- title:
--   Global Theory: pairing surjective of separating
-- statement:
--   The Global Theory construction uses the pairing surjective of separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorProductNondegeneratePairing.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorProductNondegeneratePairing.lean#L7-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorProductNondegeneratePairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module

theorem GlobalTheory.pairing_surjective_of_separating {M N : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N] (b : M →ₗ[ℂ] N →ₗ[ℂ] ℂ)
    (hb : ∀ u, u ≠ 0 → ∃ v, b v u ≠ 0) : Function.Surjective b := by sorry
