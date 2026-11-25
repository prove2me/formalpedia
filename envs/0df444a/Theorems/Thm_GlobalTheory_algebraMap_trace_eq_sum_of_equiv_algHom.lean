-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_trace_eq_sum_of_equiv_algHom
-- name    : GlobalTheory.algebraMap_trace_eq_sum_of_equiv_algHom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:05.136102+00:00
-- url     : https://prove2.me/theorems/0b134013-e1c9-4fdc-b031-b742365e293e
-- title:
--   Global Theory: algebra Map trace eq sum of equiv alg Hom
-- statement:
--   The Global Theory construction uses the algebra Map trace eq sum of equiv alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L290-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L290-L293

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

theorem GlobalTheory.algebraMap_trace_eq_sum_of_equiv_algHom (P : ι ≃ (S →ₐ[K] L)) (x : S) :
    algebraMap K L (Algebra.trace K S x) = ∑ j, P j x := by sorry
