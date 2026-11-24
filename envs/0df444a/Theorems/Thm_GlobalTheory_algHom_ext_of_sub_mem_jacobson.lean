-- Prove2me | Theorems.Thm_GlobalTheory_algHom_ext_of_sub_mem_jacobson
-- name    : GlobalTheory.algHom_ext_of_sub_mem_jacobson
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:40.090465+00:00
-- url     : https://prove2.me/theorems/c2dfb97b-1a1b-4516-ae29-30e95ccf7fd7
-- title:
--   Global Theory: alg Hom ext of sub mem jacobson
-- statement:
--   The Global Theory construction uses the alg Hom ext of sub mem jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L24-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L24-L52

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

theorem GlobalTheory.algHom_ext_of_sub_mem_jacobson {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]
    {f g : A →ₐ[R] B} (h : ∀ a, f a - g a ∈ (⊥ : Ideal B).jacobson) : f = g := by sorry
