-- Prove2me | Theorems.Thm_GlobalTheory_SymDesc_injective_quotient
-- name    : GlobalTheory.SymDesc.injective_quotient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:27.52249+00:00
-- url     : https://prove2.me/theorems/76125e98-98f7-46c6-b5c8-212240161e73
-- title:
--   Sym Desc: injective quotient
-- statement:
--   The Sym Desc construction uses the injective quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DescendElementOfFieldEqualizerFaithfullyFlat.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DescendElementOfFieldEqualizerFaithfullyFlat.lean#L9-L16

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

theorem GlobalTheory.SymDesc.injective_quotient (Q : Ideal R₁) (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    Function.Injective (algebraMap R (R₁ ⧸ Q)) := by sorry
