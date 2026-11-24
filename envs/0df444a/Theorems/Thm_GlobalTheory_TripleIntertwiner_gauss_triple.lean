-- Prove2me | Theorems.Thm_GlobalTheory_TripleIntertwiner_gauss_triple
-- name    : GlobalTheory.TripleIntertwiner.gauss_triple
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:34.427248+00:00
-- url     : https://prove2.me/theorems/f368354a-4f04-4d70-ba9f-33215fe274cd
-- title:
--   Triple Intertwiner: gauss triple
-- statement:
--   The Triple Intertwiner construction uses the gauss triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L255-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L255-L308

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

theorem GlobalTheory.TripleIntertwiner.gauss_triple (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A₀ A B C : AddSubgroup V} (hA : A₀ ≤ A) (hB : A₀ ≤ B) (hC : A₀ ≤ C)
    [Fintype (B ⧸ A₀.addSubgroupOf B)] [Fintype (C ⧸ A₀.addSubgroupOf C)]
    (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1) (cB : ∀ x ∈ B, ∀ y ∈ B, c x y = 1)
    (cC : ∀ x ∈ C, ∀ y ∈ C, c x y = 1) :
    (∑ z : C ⧸ A₀.addSubgroupOf C, ∑ y : B ⧸ A₀.addSubgroupOf B,
        if rep z + rep y ∈ A then c (rep z) (rep y) else 0) ^ 4 =
    (∑ y : B ⧸ A₀.addSubgroupOf B, ∑ z : C ⧸ A₀.addSubgroupOf C,
        if rep y + rep z ∈ A then c (rep y) (rep z) else 0) ^ 4 := by sorry
