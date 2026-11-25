-- Prove2me | Theorems.Thm_GlobalTheory_card_eq_finrank_of_equiv_algHom
-- name    : GlobalTheory.card_eq_finrank_of_equiv_algHom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:44.266864+00:00
-- url     : https://prove2.me/theorems/74acd129-7b9e-47da-9243-9609e36b19bb
-- title:
--   Global Theory: card eq finrank of equiv alg Hom
-- statement:
--   The Global Theory construction uses the card eq finrank of equiv alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L282-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L282-L283

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable (K : Type*) {S : Type*} (L : Type*) [Field K] [CommRing S] [Algebra K S] [Field L]
  [Algebra K L] [IsSepClosed L] [Algebra.Etale K S]
variable {K L} {ι : Type*} [Fintype ι]

theorem GlobalTheory.card_eq_finrank_of_equiv_algHom (P : ι ≃ (S →ₐ[K] L)) : Fintype.card ι = finrank K S := by sorry
