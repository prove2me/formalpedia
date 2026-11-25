-- Prove2me | Theorems.Thm_GlobalTheory_ReducedAlg_isReduced_tensor
-- name    : GlobalTheory.ReducedAlg.isReduced_tensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:16.79525+00:00
-- url     : https://prove2.me/theorems/d335a576-417c-4181-87fc-2ee2a58f055d
-- title:
--   Reduced Alg: is Reduced tensor
-- statement:
--   The Reduced Alg construction uses the is Reduced tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/EqZeroOfForallLTensorEqZero.lean#L105-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/EqZeroOfForallLTensorEqZero.lean#L105-L115

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

theorem GlobalTheory.ReducedAlg.isReduced_tensor {k : Type*} [Field k] [PerfectField k] (A B : Type*)
    [CommRing A] [Algebra k A] [IsReduced A] [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by sorry
