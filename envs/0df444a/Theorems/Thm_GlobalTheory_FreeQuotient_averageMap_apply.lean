-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_averageMap_apply
-- name    : GlobalTheory.FreeQuotient.averageMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:59.308824+00:00
-- url     : https://prove2.me/theorems/9d1e1f55-9311-4d21-a6cc-62858093534c
-- title:
--   Free Quotient: average Map apply
-- statement:
--   The Free Quotient construction uses the average Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L306-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L306-L307

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.FreeQuotient
variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]

theorem GlobalTheory.FreeQuotient.averageMap_apply (f : M →ₗ[A] N) (m : M) :
    averageMap G f m = ∑ g : G, g • f (g⁻¹ • m) := by sorry
