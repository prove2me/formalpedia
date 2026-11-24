-- Prove2me | Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_mem_irreducibleComponents_of_trdeg_eq
-- name    : GlobalTheory.topologicalKrullDim_eq_of_mem_irreducibleComponents_of_trdeg_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:57.810605+00:00
-- url     : https://prove2.me/theorems/735f9f68-405d-4b1b-b397-d73491bba883
-- title:
--   Global Theory: topological Krull Dim eq of mem irreducible Components of trdeg eq
-- statement:
--   The Global Theory construction uses the topological Krull Dim eq of mem irreducible Components of trdeg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L491-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L491-L519

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

theorem GlobalTheory.topologicalKrullDim_eq_of_mem_irreducibleComponents_of_trdeg_eq
    {S : Type*} [TopologicalSpace S]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S) {d : ℕ}
    (hd : letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
      Algebra.trdeg O Y.functionField = d) :
    topologicalKrullDim Z = d := by sorry
