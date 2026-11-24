-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_lift_of_etale_of_isLocalRing
-- name    : GlobalTheory.exists_algHom_lift_of_etale_of_isLocalRing
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:26:58.351157+00:00
-- url     : https://prove2.me/theorems/23040b14-460f-493b-b5cc-623fb62d29ea
-- title:
--   Global Theory: exists alg Hom lift of etale of is Local Ring
-- statement:
--   The Global Theory construction uses the exists alg Hom lift of etale of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L54-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L54-L97

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

theorem GlobalTheory.exists_algHom_lift_of_etale_of_isLocalRing {R A S : Type*} [CommRing R] [CommRing A]
    [CommRing S] [Algebra R A] [Algebra R S] [Algebra.Etale R A] [IsLocalRing S] (J : Ideal S)
    [HenselianRing S J] (φ : A →ₐ[R] S ⧸ J) :
    ∃ ψ : A →ₐ[R] S, ∀ a, Ideal.Quotient.mk J (ψ a) = φ a := by sorry
