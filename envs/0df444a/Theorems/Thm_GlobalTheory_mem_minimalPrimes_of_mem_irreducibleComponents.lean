-- Prove2me | Theorems.Thm_GlobalTheory_mem_minimalPrimes_of_mem_irreducibleComponents
-- name    : GlobalTheory.mem_minimalPrimes_of_mem_irreducibleComponents
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:48.193072+00:00
-- url     : https://prove2.me/theorems/25582ee6-3f78-475a-adb8-a100906e9fa0
-- title:
--   Global Theory: mem minimal Primes of mem irreducible Components
-- statement:
--   The Global Theory construction uses the mem minimal Primes of mem irreducible Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L455-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L455-L481

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
omit [IsIntegral Y] [LocallyOfFiniteType f] [Flat f]

theorem GlobalTheory.mem_minimalPrimes_of_mem_irreducibleComponents {S : Type*} [TopologicalSpace S]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S)
    {A : Type u} [CommRing A] [Algebra O A] {j : Spec (.of A) ⟶ Y} [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A)))
    {q : PrimeSpectrum A} (hq : IsGenericPoint (j q) (i '' Z)) :
    q.asIdeal ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes := by sorry
