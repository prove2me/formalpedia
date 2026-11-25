-- Prove2me | Theorems.Thm_GlobalTheory_SmoothPointCover_exists_family_near
-- name    : GlobalTheory.SmoothPointCover.exists_family_near
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:39.17625+00:00
-- url     : https://prove2.me/theorems/382f2f23-40eb-42fe-9d66-b6cadcd7ae3c
-- title:
--   Smooth Point Cover: exists family near
-- statement:
--   The Smooth Point Cover construction uses the exists family near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsCountableHolomorphicFamiliesSmooth.lean#L9-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsCountableHolomorphicFamiliesSmooth.lean#L9-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsHolomorphicFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DenseMvPolynomialEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEmbeddingsOverInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsCountableHolomorphicFamiliesSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open GlobalTheory GlobalTheory.SmoothPointCover

theorem GlobalTheory.SmoothPointCover.exists_family_near (K A : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.Smooth K A] (σ : K →+* ℂ) (φ₀ : A →+* ℂ) (h₀ : φ₀.comp (algebraMap K A) = σ) :
    ∃ (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (U : Set (A → ℂ)), U ∈ 𝓝 (φ₀ : A → ℂ) ∧
      IsOpen B ∧ (∀ b ∈ B, (φ b).comp (algebraMap K A) = σ) ∧
      (∀ a : A, DifferentiableOn ℂ (fun b => φ b a) B) ∧
      (∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → (ψ : A → ℂ) ∈ U → ∃ b ∈ B, φ b = ψ) ∧
      ∀ b ∈ B, ∀ a : A, a ≠ 0 → ∃ᶠ b' in 𝓝 b, φ b' a ≠ 0 := by sorry
