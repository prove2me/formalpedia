-- Prove2me | Theorems.Thm_GlobalTheory_bijective_algHom_comp_of_etale_of_henselian
-- name    : GlobalTheory.bijective_algHom_comp_of_etale_of_henselian
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:43:16.190628+00:00
-- url     : https://prove2.me/theorems/e63c570c-4b11-5f96-a65c-3cc8a481bd10
-- title:
--   Global Theory: bijective alg Hom comp of etale of henselian
-- statement:
--   The Global Theory construction uses the bijective alg Hom comp of etale of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L487-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L487-L500

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct

theorem GlobalTheory.bijective_algHom_comp_of_etale_of_henselian (R : Type*) {k A B C : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing k] [CommRing A] [CommRing B] [CommRing C] [Algebra R B]
    [Module.Finite R B] [Algebra k A] [Algebra k B] [Algebra k C] [Algebra.Etale k A]
    (π : B →ₐ[k] C) (hπ : Function.Surjective π)
    (hker : RingHom.ker π ≤ (⊥ : Ideal B).jacobson) :
    Function.Bijective fun ψ : A →ₐ[k] B ↦ π.comp ψ := by sorry
