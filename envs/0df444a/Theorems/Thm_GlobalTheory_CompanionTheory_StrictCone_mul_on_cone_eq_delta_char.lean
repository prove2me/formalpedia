-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_mul_on_cone_eq_delta_char
-- name    : GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:15:03.019538+00:00
-- url     : https://prove2.me/theorems/68e8e751-be3c-4c88-be2f-9b04700a6a1e
-- title:
--   Strict Cone: mul on cone eq delta char
-- statement:
--   The Strict Cone construction uses the mul on cone eq delta char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativeCharacterOnCone.lean#L115-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativeCharacterOnCone.lean#L115-L136

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativeCharacterOnCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StrictCone

theorem GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char : ∀ (a b : ℕ) (q : ℂ), q ≠ 0 → ∀ χ : (Fin a → ℤ) → (Fin b → ℤ) → ℂ, (∀ x x' y y', (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → x' j + 1 ≤ x' i) → (∀ i j, i < j → y j + 1 ≤ y i) → (∀ i j, i < j → y' j + 1 ≤ y' i) → χ (x + x') (y + y') = χ x y * χ x' y') → (∃ x y, (∀ i j, i < j → x j + 1 ≤ x i) ∧ (∀ i j, i < j → y j + 1 ≤ y i) ∧ χ x y ≠ 0) → ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ∀ x y, (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → y j + 1 ≤ y i) → χ x y = q ^ (∑ i : Fin a, ((a : ℤ) - 1 - 2 * (i : ℕ)) * x i) * (∏ i, ((ξa i ^ x i : ℂˣ) : ℂ)) * (q ^ (∑ i : Fin b, ((b : ℤ) - 1 - 2 * (i : ℕ)) * y i) * ∏ i, ((ξb i ^ y i : ℂˣ) : ℂ)) := by sorry
