-- Prove2me | Theorems.Thm_GlobalTheory_NearlyPrimitive_norm_smul_le_one_of_lt
-- name    : GlobalTheory.NearlyPrimitive.norm_smul_le_one_of_lt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:31.230008+00:00
-- url     : https://prove2.me/theorems/1d3aa1ff-c83c-41eb-829c-8ca297e336ca
-- title:
--   Nearly Primitive: norm smul le one of lt
-- statement:
--   The Nearly Primitive construction uses the norm smul le one of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L121-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L121-L229

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

theorem GlobalTheory.NearlyPrimitive.norm_smul_le_one_of_lt (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [CharZero C] (p : ℕ) [hp : Fact p.Prime] (hpn : ‖(p : C)‖ = (p : ℝ)⁻¹)
    (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂]
    (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂)
    (hs₁ : ∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) (hs₂ : ∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x)
    (hn₁ : ∀ x, 0 ≤ N₁ x) (hn₂ : ∀ x, 0 ≤ N₂ x)
    (hadd : ∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) (hmul : ∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y)
    (hΔ : ∀ x, N₂ (Δ x) ≤ N₁ x) (hij : ∀ x y, N₂ (i x * j y) = N₁ x * N₁ y)
    (y : B₁) (K : ℝ) (hK : ∀ k : ℕ, N₁ (y ^ k) ≤ K) (he : N₂ (Δ y - i y - j y) ≤ 1)
    (c : C) (hc : ‖c‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) : N₁ (c • y) ≤ 1 := by sorry
