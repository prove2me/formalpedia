-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_sumOp_comp_of_between
-- name    : GlobalTheory.FinWeil.sumOp_comp_of_between
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:29:35.5158+00:00
-- url     : https://prove2.me/theorems/c31afbb9-6ffb-43ef-89e2-bc032f860a8a
-- title:
--   Fin Weil: sum Op comp of between
-- statement:
--   The Fin Weil construction uses the sum Op comp of between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HeisenbergIntertwiningSumCompOfIntermediateLatti.lean#L10-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HeisenbergIntertwiningSumCompOfIntermediateLatti.lean#L10-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumCompOfIntermediateLatti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil

theorem GlobalTheory.FinWeil.sumOp_comp_of_between : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx B C ≠ 0 → B ≤ (B ⊓ A) ⊔ (B ⊓ C) → idx A C = idx A B * idx B C ∧ ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = sumOp W A C v := by sorry
