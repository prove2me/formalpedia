-- Prove2me | Theorems.Thm_GlobalTheory_ReducedAlg_isReduced_field_tensor
-- name    : GlobalTheory.ReducedAlg.isReduced_field_tensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:06.434427+00:00
-- url     : https://prove2.me/theorems/c0ec93f9-21a2-483c-8c4a-75efbf8092aa
-- title:
--   Reduced Alg: is Reduced field tensor
-- statement:
--   The Reduced Alg construction uses the is Reduced field tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/EqZeroOfForallLTensorEqZero.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/EqZeroOfForallLTensorEqZero.lean#L92-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.ReducedAlg

theorem GlobalTheory.ReducedAlg.isReduced_field_tensor {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsReduced A] :
    IsReduced (K ⊗[k] A) := by sorry
