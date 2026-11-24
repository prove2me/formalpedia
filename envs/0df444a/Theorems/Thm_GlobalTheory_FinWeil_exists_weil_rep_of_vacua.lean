-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_exists_weil_rep_of_vacua
-- name    : GlobalTheory.FinWeil.exists_weil_rep_of_vacua
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:26:47.465393+00:00
-- url     : https://prove2.me/theorems/625273bd-0fc1-4486-9cd5-5905a5ceb323
-- title:
--   Fin Weil: exists weil rep of vacua
-- statement:
--   The Fin Weil construction uses the exists weil rep of vacua property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsWeilRepresentationOfLatticeVacua.lean#L187-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsWeilRepresentationOfLatticeVacua.lean#L187-L318

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsWeilRepresentationOfLatticeVacua
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
open Classical
open scoped BigOperators

theorem GlobalTheory.FinWeil.exists_weil_rep_of_vacua : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam → ∀ A : Submodule R X,
    _root_.GlobalTheory.FinWeil.SelfDual γ A →
    Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ →
    ∀ {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) →
    (∀ g, _root_.GlobalTheory.FinWeil.idx A (A.map (ρ g)) ≠ 0) →
    ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧
      ∀ g, _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) ∧
        ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e →
          Om g e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e := by sorry
