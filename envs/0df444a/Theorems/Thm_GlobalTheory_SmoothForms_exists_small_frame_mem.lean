-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_exists_small_frame_mem
-- name    : GlobalTheory.SmoothForms.exists_small_frame_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:01.485314+00:00
-- url     : https://prove2.me/theorems/2c54e8b1-7ab0-4be5-872a-2e4ce0709a9e
-- title:
--   Smooth Forms: exists small frame mem
-- statement:
--   The Smooth Forms construction uses the exists small frame mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/OrthogonalAnisotropicFrameBoundedCM.lean#L51-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/OrthogonalAnisotropicFrameBoundedCM.lean#L51-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalAnisotropicFrameBoundedCM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SmoothForms.exists_small_frame_mem (n : ℕ) : ∃ k : ℕ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (N : ℤ) (ν : V → ℝ) (B₀ : ℝ), Sized h Λ N ν B₀ →
    ∀ B : ℝ, 2 ≤ B → ∀ W : Submodule E V, Module.finrank E W = n → (∀ y ∈ W, (∀ x ∈ W, h y x = 0) → y = 0) →
    W ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ ∧ v i ∈ W) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
      ∀ i, h (v i) (v i) ≠ 0 ∧ ν (v i) ≤ B ^ k := by sorry
