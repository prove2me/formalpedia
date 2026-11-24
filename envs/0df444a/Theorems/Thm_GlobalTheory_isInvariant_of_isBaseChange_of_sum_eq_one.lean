-- Prove2me | Theorems.Thm_GlobalTheory_isInvariant_of_isBaseChange_of_sum_eq_one
-- name    : GlobalTheory.isInvariant_of_isBaseChange_of_sum_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:58:13.041376+00:00
-- url     : https://prove2.me/theorems/9d267472-1edb-4422-ad04-76dd42e1c960
-- title:
--   Global Theory: is Invariant of is Base Change of sum eq one
-- statement:
--   The Global Theory construction uses the is Invariant of is Base Change of sum eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L159-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L159-L189

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type*} [Group G] [Fintype G] {B B' A A' : Type*} [CommRing B] [CommRing B']
  [CommRing A] [CommRing A'] [Algebra B B'] [Algebra B A] [Algebra B A'] [Algebra B' A']
  [IsScalarTower B B' A'] [MulSemiringAction G A] [SMulCommClass G B A] [MulSemiringAction G A']
  [SMulCommClass G B' A'] [FaithfulSMul B A] [Algebra.IsInvariant B A G]

theorem GlobalTheory.isInvariant_of_isBaseChange_of_sum_eq_one {c : A} (hc : ∑ g : G, g • c = 1)
    (f : A →ₐ[B] A') (hb : IsBaseChange B' f.toLinearMap)
    (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    FaithfulSMul B' A' ∧ Algebra.IsInvariant B' A' G := by sorry
