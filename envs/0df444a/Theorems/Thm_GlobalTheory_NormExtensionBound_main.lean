-- Prove2me | Theorems.Thm_GlobalTheory_NormExtensionBound_main
-- name    : GlobalTheory.NormExtensionBound.main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:49.386156+00:00
-- url     : https://prove2.me/theorems/c6cb1ef1-a0a7-4268-8f38-20aaf467a8c3
-- title:
--   Norm Extension Bound: main
-- statement:
--   The Norm Extension Bound construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeOneOfExtension.lean#L72-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeOneOfExtension.lean#L72-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeOneOfExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormExtensionBound
open scoped Pointwise

theorem GlobalTheory.NormExtensionBound.main : ∀ (p : ℕ) [Fact (Nat.Prime p)] (A B : Type) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)]
    (𝔷 : Ideal B), Function.Injective (algebraMap A B) →
    (∀ (b : B), (∀ (σ : B ≃ₐ[A] B), σ b = b) → b ∈ Set.range (algebraMap A B)) →
    Ideal.IsMaximal 𝔷 → ∀ (ev : A →+* PadicAlgCl p), (∀ (a : A), ‖ev a‖ ≤ (1 : ℝ)) →
    (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < (1 : ℝ)) →
    ∃ (ev' : B →+* PadicAlgCl p), (∀ (a : A), ev' (algebraMap A B a) = ev a) ∧
      (∀ (b : B), ‖ev' b‖ ≤ (1 : ℝ)) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < (1 : ℝ) := by sorry
