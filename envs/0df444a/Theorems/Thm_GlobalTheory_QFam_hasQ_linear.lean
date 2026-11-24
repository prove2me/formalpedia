-- Prove2me | Theorems.Thm_GlobalTheory_QFam_hasQ_linear
-- name    : GlobalTheory.QFam.hasQ_linear
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:13:26.977733+00:00
-- url     : https://prove2.me/theorems/b6750a9a-12e3-44e5-8acc-f296bb17f980
-- title:
--   QFam: has Q linear
-- statement:
--   The QFam construction uses the has Q linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelLinearOperations.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelLinearOperations.lean#L37-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.hasQ_linear : ∀ (N : ℕ), (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ + g τ) (fun n => a n + b n)) ∧ (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ - g τ) (fun n => a n - b n)) ∧ (∀ (c : ℂ) f a, HasQ N f a → HasQ N (fun τ => c * f τ) (fun n => c * a n)) ∧ (∀ c : ℂ, HasQ N (fun _ => c) (fun n => if n = 0 then c else 0)) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ) (a : κ → ℕ → ℂ), (∀ k ∈ s, HasQ N (f k) (a k)) → HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n)) := by sorry
