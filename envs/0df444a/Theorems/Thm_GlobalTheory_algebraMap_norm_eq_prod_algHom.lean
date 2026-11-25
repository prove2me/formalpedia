-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_norm_eq_prod_algHom
-- name    : GlobalTheory.algebraMap_norm_eq_prod_algHom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:22.309577+00:00
-- url     : https://prove2.me/theorems/79d2be35-2b9f-5a6b-b689-73ca9ae264f3
-- title:
--   Global Theory: algebra Map norm eq prod alg Hom
-- statement:
--   The Global Theory construction uses the algebra Map norm eq prod alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L266-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L266-L271

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

theorem GlobalTheory.algebraMap_norm_eq_prod_algHom [Fintype (S →ₐ[K] L)] (x : S) :
    algebraMap K L (Algebra.norm K x) = ∏ P : S →ₐ[K] L, P x := by sorry
