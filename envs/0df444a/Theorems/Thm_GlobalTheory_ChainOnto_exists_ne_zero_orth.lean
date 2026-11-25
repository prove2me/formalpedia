-- Prove2me | Theorems.Thm_GlobalTheory_ChainOnto_exists_ne_zero_orth
-- name    : GlobalTheory.ChainOnto.exists_ne_zero_orth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:20:27.958259+00:00
-- url     : https://prove2.me/theorems/2524016b-de7a-529f-aa13-4d247843757c
-- title:
--   Chain Onto: exists ne zero orth
-- statement:
--   The Chain Onto construction uses the exists ne zero orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SurjectiveOfAdjointSeparatesLabelledParts.lean#L85-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SurjectiveOfAdjointSeparatesLabelledParts.lean#L85-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SurjectiveOfAdjointSeparatesLabelledParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ChainOnto

theorem GlobalTheory.ChainOnto.exists_ne_zero_orth {A : Type} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ipA x y = conj (ipA y x))
    (S : Submodule ℂ A) (hS : S ≠ ⊤) : ∃ u : A, u ≠ 0 ∧ ∀ s ∈ S, ipA s u = 0 := by sorry
