-- Prove2me | Theorems.Thm_GlobalTheory_DualFrames_dual_of_dual_frames
-- name    : GlobalTheory.DualFrames.dual_of_dual_frames
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:07.115035+00:00
-- url     : https://prove2.me/theorems/ded29c5e-fab9-427a-a066-c596b67e0e70
-- title:
--   Dual Frames: dual of dual frames
-- statement:
--   The Dual Frames construction uses the dual of dual frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DualOfDualFrames.lean#L46-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DualOfDualFrames.lean#L46-L107

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DualOfDualFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.DualFrames
variable {A : Type} [CommRing A] {k : ℕ}

theorem GlobalTheory.DualFrames.dual_of_dual_frames :
    ∀ (A : Type) [CommRing A] (S : Subring A) (τ : A →+* A), (∀ a, τ (τ a) = a) →
      (∀ a ∈ S, τ a ∈ S) → ∀ (k : ℕ) (J : Matrix (Fin k) (Fin k) A), IsHerm τ J →
      ∀ (B C : GL (Fin k) A) (L₁ L₂ : Submodule S (Fin k → A)),
      cT τ (B : Matrix (Fin k) (Fin k) A) * J * (C : Matrix (Fin k) (Fin k) A) = 1 →
      (∀ y : Fin k → A, (B : Matrix (Fin k) (Fin k) A) *ᵥ y ∈ L₁ ↔ ∀ i, y i ∈ S) →
      (∀ y : Fin k → A, (C : Matrix (Fin k) (Fin k) A) *ᵥ y ∈ L₂ ↔ ∀ i, y i ∈ S) →
      (∀ y, y ∈ L₂ ↔ ∀ x ∈ L₁, hform τ J x y ∈ S) ∧
      (∀ y, y ∈ L₁ ↔ ∀ x ∈ L₂, hform τ J x y ∈ S) ∧
      (∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform τ J x y ∈ S) := by sorry
