-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_countable_holomorphic_families_smooth
-- name    : GlobalTheory.T.exists_countable_holomorphic_families_smooth
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:30:12.652061+00:00
-- url     : https://prove2.me/theorems/064435b6-4ad2-53ed-a1a4-2669d66fdf1e
-- title:
--   T: exists countable holomorphic families smooth
-- statement:
--   The T construction uses the exists countable holomorphic families smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsCountableHolomorphicFamiliesSmoothStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsCountableHolomorphicFamiliesSmoothStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsCountableHolomorphicFamiliesSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsHolomorphicFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DenseMvPolynomialEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEmbeddingsOverInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsCountableHolomorphicFamiliesSmoothStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_countable_holomorphic_families_smooth : ∀ (K A : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ), ∃ (ι : Type) (_ : Countable ι) (m : ι → ℕ) (B : ∀ i, Set (Fin (m i) → ℂ)) (φ : ∀ i, (Fin (m i) → ℂ) → (A →+* ℂ)), (∀ i, IsOpen (B i)) ∧ (∀ i, ∀ b ∈ B i, (φ i b).comp (algebraMap K A) = σ) ∧ (∀ i (a : A), DifferentiableOn ℂ (fun b => φ i b a) (B i)) ∧ (∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → ∃ i, ∃ b ∈ B i, φ i b = ψ) ∧ ∀ i, ∀ b ∈ B i, ∀ a : A, a ≠ 0 → ∃ᶠ b' in 𝓝 b, φ i b' a ≠ 0 := by sorry
