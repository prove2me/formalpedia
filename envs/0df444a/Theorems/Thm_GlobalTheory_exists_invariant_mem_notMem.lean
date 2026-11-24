-- Prove2me | Theorems.Thm_GlobalTheory_exists_invariant_mem_notMem
-- name    : GlobalTheory.exists_invariant_mem_notMem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:13.162708+00:00
-- url     : https://prove2.me/theorems/34dd447b-9d79-4c61-8156-f52c01f0f92d
-- title:
--   Global Theory: exists invariant mem not Mem
-- statement:
--   The Global Theory construction uses the exists invariant mem not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L18-L32

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
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]

theorem GlobalTheory.exists_invariant_mem_notMem (q : Ideal A) [hq : q.IsPrime] (I : Ideal A)
    (h : ∀ g : G, ¬ I ≤ g • q) : ∃ t ∈ I, (∀ g : G, g • t = t) ∧ t ∉ q := by sorry
