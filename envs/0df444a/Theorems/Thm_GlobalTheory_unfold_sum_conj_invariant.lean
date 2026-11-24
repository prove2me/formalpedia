-- Prove2me | Theorems.Thm_GlobalTheory_unfold_sum_conj_invariant
-- name    : GlobalTheory.unfold_sum_conj_invariant
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:37.928624+00:00
-- url     : https://prove2.me/theorems/cdf8bf3a-907b-409c-b6e3-bd8b4a52aaa3
-- title:
--   Global Theory: unfold sum conj invariant
-- statement:
--   The Global Theory construction uses the unfold sum conj invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnfoldSumInvariantLeviConj.lean#L5-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnfoldSumInvariantLeviConj.lean#L5-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnfoldSumInvariantLeviConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.unfold_sum_conj_invariant : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → ∀ k ∈ KM, ∀ y : P, (∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * ((s k)⁻¹ * y * s k) * u (Quotient.out x))) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by sorry
