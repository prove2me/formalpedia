-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_trace_eq_sum_algHom
-- name    : GlobalTheory.algebraMap_trace_eq_sum_algHom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:23.497825+00:00
-- url     : https://prove2.me/theorems/6fa7a624-9451-5803-93b6-e544c12b8c46
-- title:
--   Global Theory: algebra Map trace eq sum alg Hom
-- statement:
--   The Global Theory construction uses the algebra Map trace eq sum alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L273-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L273-L278

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

theorem GlobalTheory.algebraMap_trace_eq_sum_algHom [Fintype (S →ₐ[K] L)] (x : S) :
    algebraMap K L (Algebra.trace K S x) = ∑ P : S →ₐ[K] L, P x := by sorry
