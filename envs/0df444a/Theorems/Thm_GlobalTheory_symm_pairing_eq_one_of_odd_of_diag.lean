-- Prove2me | Theorems.Thm_GlobalTheory_symm_pairing_eq_one_of_odd_of_diag
-- name    : GlobalTheory.symm_pairing_eq_one_of_odd_of_diag
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:22:57.45209+00:00
-- url     : https://prove2.me/theorems/fe05eaca-1d17-453a-978a-d3f98f8c1f73
-- title:
--   Global Theory: symm pairing eq one of odd of diag
-- statement:
--   The Global Theory construction uses the symm pairing eq one of odd of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SymmPairingEqOneOfOddOfDiag.lean#L32-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SymmPairingEqOneOfOddOfDiag.lean#L32-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SymmPairingEqOneOfOddOfDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
open GlobalTheory

theorem GlobalTheory.symm_pairing_eq_one_of_odd_of_diag :
    ∀ (X U : Type) [AddCommGroup X] [CommGroup U] (d k : ℕ) (e : Module.Basis (Fin d) ℤ X) (b : ℤ), Odd k → (k : ℤ) ∣ 2 * b - 1 → ∀ δ : X → X → U, (∀ x x' y, δ (x + x') y = δ x y * δ x' y) → (∀ x y, δ x y = δ y x) → (∀ x y, δ x y ^ k = 1) → (∀ i, δ (e i) (e i) ^ b = 1) → (∀ i j, δ (e i + e j) (e i + e j) ^ b = 1) → ∀ x y, δ x y = 1 := by sorry
