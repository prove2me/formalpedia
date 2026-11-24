-- Prove2me | Theorems.Thm_GlobalTheory_TripleIntertwiner_itw_eq
-- name    : GlobalTheory.TripleIntertwiner.itw_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:11.424745+00:00
-- url     : https://prove2.me/theorems/802b2044-e47b-40bf-82ba-81ead8c2a388
-- title:
--   Triple Intertwiner: itw eq
-- statement:
--   The Triple Intertwiner construction uses the itw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L145-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L145-L177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]
variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}

theorem GlobalTheory.TripleIntertwiner.itw_eq (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A₀ A B : AddSubgroup V} (hA : A₀ ≤ A) (hB : A₀ ≤ B)
    [Fintype (B ⧸ A₀.addSubgroupOf B)] (cB : ∀ x ∈ B, ∀ y ∈ B, c x y = 1)
    (f : F) (hf : ∀ x ∈ A, W x f = f) :
    ∃ ρ : ℂ, ρ ^ 2 * ((A₀.relIndex B : ℂ) * (A₀.relIndex (A ⊓ B) : ℂ)) = 1 ∧
      itw W A B f = ρ • ∑ q : B ⧸ A₀.addSubgroupOf B, W (rep q) f := by sorry
