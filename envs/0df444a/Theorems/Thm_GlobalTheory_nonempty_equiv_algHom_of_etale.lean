-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_equiv_algHom_of_etale
-- name    : GlobalTheory.nonempty_equiv_algHom_of_etale
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:36.177581+00:00
-- url     : https://prove2.me/theorems/d3f99cba-260a-4fbd-90e0-03f32994d88b
-- title:
--   Global Theory: nonempty equiv alg Hom of etale
-- statement:
--   The Global Theory construction uses the nonempty equiv alg Hom of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L260-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L260-L264

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
variable (S)

theorem GlobalTheory.nonempty_equiv_algHom_of_etale {ι : Type*} [Fintype ι] (h : Fintype.card ι = finrank K S) :
    Nonempty (ι ≃ (S →ₐ[K] L)) := by sorry
