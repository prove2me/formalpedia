-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentDecomposition_main
-- name    : GlobalTheory.UnipotentDecomposition.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:25:57.128798+00:00
-- url     : https://prove2.me/theorems/f748654e-c158-4bbb-95be-1ca19e6e56c4
-- title:
--   Unipotent Decomposition: main
-- statement:
--   The Unipotent Decomposition construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UdlApply.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UdlApply.lean#L98-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentDecomposition
open Matrix

theorem GlobalTheory.UnipotentDecomposition.main : (let d1 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (β : O) (l : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → l i j = (0 : O)) ∧ (i = j → l i j = (1 : O)) ∧ (j < i → β ∣ l i j)); let d2 : {O : Type} → [CommRing O] → {n : ℕ} → O → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α β : O) (g : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)); let d3 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α : O) (u : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (j < i → u i j = (0 : O)) ∧ (i = j → u i j = (1 : O)) ∧ (i < j → α ∣ u i j)); ∀ {O : Type} [inst : CommRing O] [IsLocalRing O] {α β : O}, ¬IsUnit (α * β) → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), d2 α β g → (∀ (i : Fin n), IsUnit (g i i)) → ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O), d3 α u ∧ d1 β l ∧ g = (u * Matrix.diagonal fun (i : Fin n) ↦ (↑(d i) : O)) * l ∧ ∀ (i : Fin n), α * β ∣ (↑(d i) : O) - g i i) := by sorry
