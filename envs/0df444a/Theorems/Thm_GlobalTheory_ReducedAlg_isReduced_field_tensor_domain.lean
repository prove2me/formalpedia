-- Prove2me | Theorems.Thm_GlobalTheory_ReducedAlg_isReduced_field_tensor_domain
-- name    : GlobalTheory.ReducedAlg.isReduced_field_tensor_domain
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:21.871587+00:00
-- url     : https://prove2.me/theorems/8fc790a3-cb8f-46bb-88ed-b6b2d87d89f6
-- title:
--   Reduced Alg: is Reduced field tensor domain
-- statement:
--   The Reduced Alg construction uses the is Reduced field tensor domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/EqZeroOfForallLTensorEqZero.lean#L61-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/EqZeroOfForallLTensorEqZero.lean#L61-L90

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

theorem GlobalTheory.ReducedAlg.isReduced_field_tensor_domain {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsDomain A] [Algebra.FiniteType k A] :
    IsReduced (K ⊗[k] A) := by sorry
