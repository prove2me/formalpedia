-- Prove2me | Theorems.Thm_GlobalTheory_SimAlg_similitude_algebraic
-- name    : GlobalTheory.SimAlg.similitude_algebraic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:12:40.347745+00:00
-- url     : https://prove2.me/theorems/32fd709a-1109-4707-8ecc-3eca512b2f15
-- title:
--   Sim Alg: similitude algebraic
-- statement:
--   The Sim Alg construction uses the similitude algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L213-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L213-L271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg

theorem GlobalTheory.SimAlg.similitude_algebraic : ∀ (Λ : Type) [AddCommGroup Λ] (Q : Λ → ℤ) (φ : Module.End ℤ Λ) (e : Λ) (q l r : ℕ), 2 ≤ l → (∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) → (∀ x, 0 ≤ Q x) → (∀ x, Q x = 0 → x = 0) → (∀ x, Q (φ x) = q * Q x) → (∀ n : ℕ, ∃ (χ : Polynomial ℤ) (y : Λ), χ.Monic ∧ χ.natDegree = r ∧ Polynomial.aeval φ χ e = l ^ n • y) → ∃ P : Polynomial ℤ, P ≠ 0 ∧ Polynomial.aeval φ P e = 0 ∧ ∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q := by sorry
