-- Prove2me | Theorems.Thm_GlobalTheory_SymDesc_eq_of_sub_mem
-- name    : GlobalTheory.SymDesc.eq_of_sub_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:23:55.646737+00:00
-- url     : https://prove2.me/theorems/3cfd46ac-2e1b-4f79-9c3f-7b93285227e9
-- title:
--   Sym Desc: eq of sub mem
-- statement:
--   The Sym Desc construction uses the eq of sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DescendElementOfFieldEqualizerFaithfullyFlat.lean#L68-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DescendElementOfFieldEqualizerFaithfullyFlat.lean#L68-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemRangeOfForallAlgHomEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DescendElementOfFieldEqualizerFaithfullyFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SymDesc
variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Algebra R R₁]

theorem GlobalTheory.SymDesc.eq_of_sub_mem [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q Q' : Ideal R₁) [Q.IsPrime] [Q'.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥)
    (hQ' : Q'.comap (algebraMap R R₁) = ⊥) (e e' : R) (he : s - algebraMap R R₁ e ∈ Q)
    (he' : s - algebraMap R R₁ e' ∈ Q') : e = e' := by sorry
