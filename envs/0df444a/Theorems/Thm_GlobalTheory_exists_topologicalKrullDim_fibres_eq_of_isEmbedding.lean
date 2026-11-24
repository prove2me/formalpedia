-- Prove2me | Theorems.Thm_GlobalTheory_exists_topologicalKrullDim_fibres_eq_of_isEmbedding
-- name    : GlobalTheory.exists_topologicalKrullDim_fibres_eq_of_isEmbedding
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:29.922699+00:00
-- url     : https://prove2.me/theorems/ad198aef-8cb2-420f-be97-e2942a615c45
-- title:
--   Global Theory: exists topological Krull Dim fibres eq of is Embedding
-- statement:
--   The Global Theory construction uses the exists topological Krull Dim fibres eq of is Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L539-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L539-L551

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

theorem GlobalTheory.exists_topologicalKrullDim_fibres_eq_of_isEmbedding
    {S G : Type*} [TopologicalSpace S] [TopologicalSpace G]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {i' : G → Y} (hi' : IsEmbedding i')
    (hr' : Set.range i' = f ⁻¹' {genericPoint (Spec (.of O))}) :
    ∃ d : ℕ, topologicalKrullDim G = d ∧
      ∀ Z ∈ irreducibleComponents S, topologicalKrullDim Z = d := by sorry
