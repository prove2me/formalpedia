-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WittFrame_unitary_adapted_triangularises
-- name    : GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:15.980797+00:00
-- url     : https://prove2.me/theorems/6bf736ef-ef49-4f09-8215-49848c47d142
-- title:
--   Witt Frame: unitary adapted triangularises
-- statement:
--   The Witt Frame construction uses the unitary adapted triangularises property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitaryExtensionOfBlock.lean#L85-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitaryExtensionOfBlock.lean#L85-L122

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryExtensionOfBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WittFrame

theorem GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ),
    J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' →
    Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ U₀ ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ (s : Matrix (Fin n) (Fin n) ℂ) (b b' : Matrix (Fin D) (Fin D) ℂ)
        (t : Matrix (Fin m) (Fin m) ℂ),
        s * C = C * b → s * (R * U₀) = (R * U₀) * t → s * (J * C) = (J * C) * b' →
        b.BlockTriangular id → t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) →
        (Uᴴ * s * U).BlockTriangular id := by sorry
