-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_weil_representation_of_lattice_vacua
-- name    : GlobalTheory.T.exists_weil_representation_of_lattice_vacua
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:35.503661+00:00
-- url     : https://prove2.me/theorems/89632ca6-0714-4857-bfbc-7db6e271a26f
-- title:
--   T: exists weil representation of lattice vacua
-- statement:
--   The T construction uses the exists weil representation of lattice vacua property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsWeilRepresentationOfLatticeVacuaStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsWeilRepresentationOfLatticeVacuaStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsWeilRepresentationOfLatticeVacua
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsWeilRepresentationOfLatticeVacuaStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_weil_representation_of_lattice_vacua : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) → (∀ g, idx A (A.map (ρ g)) ≠ 0) → ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧ ∀ g, SelfDual γ (A.map (ρ g)) ∧ ∀ e, Fixes W A e → Om g e = normOp lam W A (A.map (ρ g)) e := by sorry
