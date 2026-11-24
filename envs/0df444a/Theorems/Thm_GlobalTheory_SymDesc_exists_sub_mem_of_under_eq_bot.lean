-- Prove2me | Theorems.Thm_GlobalTheory_SymDesc_exists_sub_mem_of_under_eq_bot
-- name    : GlobalTheory.SymDesc.exists_sub_mem_of_under_eq_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:23:44.911739+00:00
-- url     : https://prove2.me/theorems/18a3abc9-f2f3-4761-b2d3-4b92246ede81
-- title:
--   Sym Desc: exists sub mem of under eq bot
-- statement:
--   The Sym Desc construction uses the exists sub mem of under eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DescendElementOfFieldEqualizerFaithfullyFlat.lean#L18-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DescendElementOfFieldEqualizerFaithfullyFlat.lean#L18-L66

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

theorem GlobalTheory.SymDesc.exists_sub_mem_of_under_eq_bot [IsIntegrallyClosed R] [CharZero R]
    [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q : Ideal R₁) [Q.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    ∃ e : R, s - algebraMap R R₁ e ∈ Q := by sorry
