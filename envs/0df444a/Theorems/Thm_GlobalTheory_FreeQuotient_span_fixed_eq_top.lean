-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_span_fixed_eq_top
-- name    : GlobalTheory.FreeQuotient.span_fixed_eq_top
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:35.583793+00:00
-- url     : https://prove2.me/theorems/dc27ddf7-ed02-4d6e-a117-1146b1357e37
-- title:
--   Free Quotient: span fixed eq top
-- statement:
--   The Free Quotient construction uses the span fixed eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L259-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L259-L289

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

theorem GlobalTheory.FreeQuotient.span_fixed_eq_top [Module.Finite A M]
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P)
    (hM : ∀ P : Ideal A, P.IsMaximal → ∀ g ∈ P.inertia G, ∀ m : M,
      g • m - m ∈ P • (⊤ : Submodule A M)) :
    Submodule.span A {m : M | ∀ g : G, g • m = m} = ⊤ := by sorry
