-- Prove2me | Theorems.Thm_GlobalTheory_ringKrullDim_stalk_eq_one_of_mem_irreducibleComponents
-- name    : GlobalTheory.ringKrullDim_stalk_eq_one_of_mem_irreducibleComponents
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:18:53.469734+00:00
-- url     : https://prove2.me/theorems/cc6f0833-4ea3-472d-936f-5d9766a4a675
-- title:
--   Global Theory: ring Krull Dim stalk eq one of mem irreducible Components
-- statement:
--   The Global Theory construction uses the ring Krull Dim stalk eq one of mem irreducible Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L521-L537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L521-L537

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

theorem GlobalTheory.ringKrullDim_stalk_eq_one_of_mem_irreducibleComponents
    {S : Type*} [TopologicalSpace S]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S) {z : S} (hz : IsGenericPoint z Z) :
    ringKrullDim (Y.presheaf.stalk (i z)) = 1 := by sorry
