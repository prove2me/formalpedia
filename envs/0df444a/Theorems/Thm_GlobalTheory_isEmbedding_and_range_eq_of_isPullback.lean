-- Prove2me | Theorems.Thm_GlobalTheory_isEmbedding_and_range_eq_of_isPullback
-- name    : GlobalTheory.isEmbedding_and_range_eq_of_isPullback
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:46.202301+00:00
-- url     : https://prove2.me/theorems/4c7f18c9-da2f-49f7-bfc3-b78be289a1ef
-- title:
--   Global Theory: is Embedding and range eq of is Pullback
-- statement:
--   The Global Theory construction uses the is Embedding and range eq of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L562-L568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L562-L568

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology Limits
variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]
variable [IsDiscreteValuationRing O]
omit [IsDomain O] [IsDiscreteValuationRing O] [IsIntegral Y] [LocallyOfFiniteType f] [Flat f]

theorem GlobalTheory.isEmbedding_and_range_eq_of_isPullback {T P : Scheme.{u}} {g : T ⟶ Spec (.of O)}
    [IsPreimmersion g] {i : P ⟶ Y} {p : P ⟶ T} (h : IsPullback i p f g) :
    IsEmbedding i ∧ Set.range i = f ⁻¹' Set.range g := by sorry
