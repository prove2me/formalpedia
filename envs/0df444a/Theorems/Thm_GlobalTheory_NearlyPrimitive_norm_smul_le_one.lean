-- Prove2me | Theorems.Thm_GlobalTheory_NearlyPrimitive_norm_smul_le_one
-- name    : GlobalTheory.NearlyPrimitive.norm_smul_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:34.274809+00:00
-- url     : https://prove2.me/theorems/907e0afd-9e53-4997-82a0-32f737075c6e
-- title:
--   Nearly Primitive: norm smul le one
-- statement:
--   The Nearly Primitive construction uses the norm smul le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L231-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L231-L254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology

theorem GlobalTheory.NearlyPrimitive.norm_smul_le_one : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂] (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂), (∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) → (∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ N₂ x) → (∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) → (∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y) → (∀ x, N₂ (Δ x) ≤ N₁ x) → (∀ x y, N₂ (i x * j y) = N₁ x * N₁ y) → ∀ y : B₁, (∃ K : ℝ, ∀ k : ℕ, N₁ (y ^ k) ≤ K) → N₂ (Δ y - i y - j y) ≤ 1 → ∀ a : C, ‖a‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → N₁ (a • y) ≤ 1 := by sorry
