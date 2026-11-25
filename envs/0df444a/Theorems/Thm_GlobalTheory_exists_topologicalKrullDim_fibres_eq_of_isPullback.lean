-- Prove2me | Theorems.Thm_GlobalTheory_exists_topologicalKrullDim_fibres_eq_of_isPullback
-- name    : GlobalTheory.exists_topologicalKrullDim_fibres_eq_of_isPullback
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:15.775528+00:00
-- url     : https://prove2.me/theorems/29bbfe48-7682-5b3a-982a-5f1a3f2e7b40
-- title:
--   Global Theory: exists topological Krull Dim fibres eq of is Pullback
-- statement:
--   The Global Theory construction uses the exists topological Krull Dim fibres eq of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L570-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L570-L606

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

theorem GlobalTheory.exists_topologicalKrullDim_fibres_eq_of_isPullback
    (K k : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    [Field k] [Algebra O k] (hk : Function.Surjective (algebraMap O k))
    {Y₀ Y₁ : Scheme.{u}} {i₀ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Spec (.of k)} {i₁ : Y₁ ⟶ Y}
    {p₁ : Y₁ ⟶ Spec (.of K)}
    (h₀ : IsPullback i₀ p₀ f (Spec.map (CommRingCat.ofHom (algebraMap O k))))
    (h₁ : IsPullback i₁ p₁ f (Spec.map (CommRingCat.ofHom (algebraMap O K)))) :
    ∃ d : ℕ, topologicalKrullDim Y₁ = d ∧ ∀ Z ∈ irreducibleComponents Y₀,
      topologicalKrullDim Z = d ∧
        ∀ z, IsGenericPoint z Z → ringKrullDim (Y.presheaf.stalk (i₀ z)) = 1 := by sorry
