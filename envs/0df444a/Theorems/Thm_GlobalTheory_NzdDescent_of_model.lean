-- Prove2me | Theorems.Thm_GlobalTheory_NzdDescent_of_model
-- name    : GlobalTheory.NzdDescent.of_model
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:36:46.300804+00:00
-- url     : https://prove2.me/theorems/6870d5a3-453a-40d4-8e7c-9b351252d0f1
-- title:
--   Nzd Descent: of model
-- statement:
--   The Nzd Descent construction uses the of model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonZeroDivisorLocalizationGeneralOfNoetherian.lean#L31-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonZeroDivisorLocalizationGeneralOfNoetherian.lean#L31-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreGoingDownTensorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonZeroDivisorLocalizationGeneralOfNoetherian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NzdDescent
open TensorProduct GlobalTheory.SmoothDescent

theorem GlobalTheory.NzdDescent.of_model (hN : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0)) (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (S B₁ : Type) (b g : B) [CommRing S] [IsNoetherianRing S] [Algebra S A] [CommRing B₁] [Algebra S B₁]
    [Algebra.Smooth S B₁] (e : A ⊗[S] B₁ ≃ₐ[A] B) (b₁ g₁ : B₁)
    (hinj : Function.Injective (fun x : B₁ => e (1 ⊗ₜ x))) (hb : e (1 ⊗ₜ b₁) = b) (hg : e (1 ⊗ₜ g₁) = g)
    (u : PrimeSpectrum B) (hgb : g * b = 0)
    (hmin : ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q) :
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by sorry
