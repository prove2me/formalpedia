-- Prove2me | Theorems.Thm_GlobalTheory_commuting_multiplier_eq_const_smul_generator
-- name    : GlobalTheory.commuting_multiplier_eq_const_smul_generator
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:11:42.931321+00:00
-- url     : https://prove2.me/theorems/c5e5ffd3-2932-470e-97d4-ccf71c46c6b9
-- title:
--   Global Theory: commuting multiplier eq const smul generator
-- statement:
--   The Global Theory construction uses the commuting multiplier eq const smul generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommutingMultiplierEqConstSmulGenerator.lean#L6-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommutingMultiplierEqConstSmulGenerator.lean#L6-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommutingMapEqSmulMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommutingMultiplierEqConstSmulGenerator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.commuting_multiplier_eq_const_smul_generator
    (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B]
    (σ : K →+* ℂ) (rd : A →+* B)
    (hsemi : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f)
    (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A)
    [FiniteDimensional K V] [FiniteDimensional K V']
    (hV : ∀ f ∈ V, rd f ∈ R) (hV' : ∀ f ∈ V', rd f ∈ R)
    (hind : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (hind' : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (h h' : B) (hh : h ∈ R) (hh' : h' ∈ R) (hhh : h * h' = 1)
    (hsub : ∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A)))
    (T : V →ₗ[K] V') (hT : T ≠ 0)
    (hcomm : ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by sorry
