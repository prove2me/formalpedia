-- Prove2me | Theorems.Thm_GlobalTheory_tensorLift_injective_of_flat
-- name    : GlobalTheory.tensorLift_injective_of_flat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:40.077321+00:00
-- url     : https://prove2.me/theorems/35e11683-f01e-4e9a-8526-bf39df54d084
-- title:
--   Global Theory: tensor Lift injective of flat
-- statement:
--   The Global Theory construction uses the tensor Lift injective of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrExtensionOfEssentiallyEtaleLocal.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrExtensionOfEssentiallyEtaleLocal.lean#L8-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrExtensionOfEssentiallyEtaleLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory

theorem GlobalTheory.tensorLift_injective_of_flat {R S A K L : Type} [CommRing R] [CommRing S] [IsDomain S]
    [CommRing A] [Field K] [Field L] [Algebra R S] [Module.Flat R S] [Algebra R A] [Algebra R K]
    [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] (i : A →ₐ[R] K)
    (hi : Function.Injective i) (f : K →+* L)
    (hf : ∀ r, f (algebraMap R K r) = algebraMap S L (algebraMap R S r)) (g : A ⊗[R] S →+* L)
    (hg : ∀ a s, g (a ⊗ₜ s) = f (i a) * algebraMap S L s) : Function.Injective g := by sorry
