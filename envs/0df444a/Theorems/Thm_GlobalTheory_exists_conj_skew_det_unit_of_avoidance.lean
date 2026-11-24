-- Prove2me | Theorems.Thm_GlobalTheory_exists_conj_skew_det_unit_of_avoidance
-- name    : GlobalTheory.exists_conj_skew_det_unit_of_avoidance
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:19.978111+00:00
-- url     : https://prove2.me/theorems/f3a6f0ea-42e5-4ee5-8e47-2d856aa3ec6c
-- title:
--   Global Theory: exists conj skew det unit of avoidance
-- statement:
--   The Global Theory construction uses the exists conj skew det unit of avoidance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConjSkewDetUnitOfAvoidance.lean#L6-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConjSkewDetUnitOfAvoidance.lean#L6-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsConjSkewDetUnitOfAvoidance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory

theorem GlobalTheory.exists_conj_skew_det_unit_of_avoidance :
  ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (c : R →+* R), (∀ r, c (c r) = r) → (∀ t : F, c (algebraMap F R t) = algebraMap F R t) → ∀ (e : R), (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) → ∀ (ρ : R), IsUnit ρ → c ρ = -ρ → ∀ {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (ε : ℤˣ), (J₀.map c)ᵀ = ((ε : ℤ) : R) • J₀ → IsUnit J₀.det → ∀ (D C x₀ : Matrix (Fin n) (Fin n) R), IsUnit (e * (D + C * x₀).det + (1 - e)) → ∃ x : Matrix (Fin n) (Fin n) R, xᵀ * J₀ + J₀ * x.map c = 0 ∧ IsUnit (e * (D + C * x).det + (1 - e)) := by sorry
