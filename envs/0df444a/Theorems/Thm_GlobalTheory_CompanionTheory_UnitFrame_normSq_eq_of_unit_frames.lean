-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnitFrame_normSq_eq_of_unit_frames
-- name    : GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:31.912686+00:00
-- url     : https://prove2.me/theorems/b863660d-2ade-48ee-b17a-aaa820a94c98
-- title:
--   Unit Frame: norm Sq eq of unit frames
-- statement:
--   The Unit Frame construction uses the norm Sq eq of unit frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitaryFramesPreserveNormSqSum.lean#L47-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitaryFramesPreserveNormSqSum.lean#L47-L65

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryFramesPreserveNormSqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnitFrame

theorem GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames : ∀ (m : ℕ), 1 ≤ m → ∀ (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ), (ζ = 1 ∨ ζ = Complex.I) → (ζ' = 1 ∨ ζ' = Complex.I) → ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1 → ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1 → ∀ v : Fin m → ℂ, ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 := by sorry
