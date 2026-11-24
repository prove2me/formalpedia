-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_lift_of_etale_of_henselian
-- name    : GlobalTheory.exists_algHom_lift_of_etale_of_henselian
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:56.198618+00:00
-- url     : https://prove2.me/theorems/51942bd0-4cb4-4e68-b1dc-c4717cb0c363
-- title:
--   Global Theory: exists alg Hom lift of etale of henselian
-- statement:
--   The Global Theory construction uses the exists alg Hom lift of etale of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L442-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L442-L485

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

theorem GlobalTheory.exists_algHom_lift_of_etale_of_henselian (R : Type*) {k A B : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing k] [CommRing A] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra k A] [Algebra k B] [Algebra.Etale k A] (J : Ideal B)
    (hJ : J ≤ (⊥ : Ideal B).jacobson) (φ : A →ₐ[k] B ⧸ J) :
    ∃ ψ : A →ₐ[k] B, ∀ a, Ideal.Quotient.mk J (ψ a) = φ a := by sorry
