-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_exists_weil_rep
-- name    : GlobalTheory.FinWeil.exists_weil_rep
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:25:31.956384+00:00
-- url     : https://prove2.me/theorems/73c21db5-65af-4793-baac-d4002763a595
-- title:
--   Fin Weil: exists weil rep
-- statement:
--   The Fin Weil construction uses the exists weil rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsWeilRepresentationHeisenberg.lean#L198-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsWeilRepresentationHeisenberg.lean#L198-L278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
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
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
open Classical
open scoped BigOperators
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.FinWeil.exists_weil_rep : ∀ {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ lam : ℕ →* ℂ,
    _root_.GlobalTheory.FinWeil.GoodNorm σ lam → ∀ A : Submodule R X, _root_.GlobalTheory.FinWeil.SelfDual γ A →
    ∀ e : M, e ≠ 0 → _root_.GlobalTheory.FinWeil.Fixes W A e →
    Submodule.span ℂ (Set.range fun x => W x e) = ⊤ → ∀ {Γ : Type} [Group Γ]
    (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) →
    (∀ g, _root_.GlobalTheory.FinWeil.idx A (A.map (ρ g)) ≠ 0) →
    ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧
      ∀ g, _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) ∧
        Om g e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e := by sorry
