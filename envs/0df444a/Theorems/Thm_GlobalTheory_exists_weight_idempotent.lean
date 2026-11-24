-- Prove2me | Theorems.Thm_GlobalTheory_exists_weight_idempotent
-- name    : GlobalTheory.exists_weight_idempotent
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:45:40.06087+00:00
-- url     : https://prove2.me/theorems/4a3e0f92-7714-46b8-8813-160c732eff09
-- title:
--   Global Theory: exists weight idempotent
-- statement:
--   The Global Theory construction uses the exists weight idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsWeightIdempotent.lean#L7-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsWeightIdempotent.lean#L7-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsWeightIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset

theorem GlobalTheory.exists_weight_idempotent (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (B T : Subgroup G)
    (lam : B →* Lˣ) (v : V) (hB : B.Normal) (hv : v ≠ 0)
    (hlam : ∀ b : B, ρ b v = (lam b : L) • v)
    (hT : ∀ g : G, g ∈ T ↔ ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b) :
    ∃ e : Module.End L V, e ≠ 0 ∧ e * e = e ∧ (∀ b : B, ρ b * e = (lam b : L) • e) ∧
      (∀ t ∈ T, ρ t * e = e * ρ t) ∧ ∀ g ∉ T, e * ρ g * e = 0 := by sorry
