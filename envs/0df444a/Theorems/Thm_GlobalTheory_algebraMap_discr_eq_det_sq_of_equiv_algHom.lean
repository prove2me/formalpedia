-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_discr_eq_det_sq_of_equiv_algHom
-- name    : GlobalTheory.algebraMap_discr_eq_det_sq_of_equiv_algHom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:23.101306+00:00
-- url     : https://prove2.me/theorems/5d4a3a6c-056d-444e-b38d-990b59384e80
-- title:
--   Global Theory: algebra Map discr eq det sq of equiv alg Hom
-- statement:
--   The Global Theory construction uses the algebra Map discr eq det sq of equiv alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L295-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L295-L299

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

theorem GlobalTheory.algebraMap_discr_eq_det_sq_of_equiv_algHom [DecidableEq ι] (P : ι ≃ (S →ₐ[K] L))
    (v : ι → S) :
    algebraMap K L (Algebra.discr K v) = (Matrix.of fun i j => P j (v i)).det ^ 2 := by sorry
