-- Prove2me | Theorems.Thm_GlobalTheory_NoCommonZeroSpread_no_common_zero_spreads
-- name    : GlobalTheory.NoCommonZeroSpread.no_common_zero_spreads
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:34:38.366466+00:00
-- url     : https://prove2.me/theorems/652561c4-865d-4f23-8254-f90fd58457ca
-- title:
--   No Common Zero Spread: no common zero spreads
-- statement:
--   The No Common Zero Spread construction uses the no common zero spreads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NoCommonZeroSpreadsConstructibleNbhd.lean#L37-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NoCommonZeroSpreadsConstructibleNbhd.lean#L37-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.NoCommonZeroSpread

theorem GlobalTheory.NoCommonZeroSpread.no_common_zero_spreads : ∀ (A : Type) [CommRing A] (τ J : Type) [Finite τ] (F : J → MvPolynomial τ A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), (¬ ∃ z : τ → Ω, ∀ j, MvPolynomial.eval₂ φ z (F j) = 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ ∃ z : τ → k, ∀ j, MvPolynomial.eval₂ ψ z (F j) = 0 := by sorry
