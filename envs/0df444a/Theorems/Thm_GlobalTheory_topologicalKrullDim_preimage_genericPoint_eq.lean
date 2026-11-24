-- Prove2me | Theorems.Thm_GlobalTheory_topologicalKrullDim_preimage_genericPoint_eq
-- name    : GlobalTheory.topologicalKrullDim_preimage_genericPoint_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:37.187033+00:00
-- url     : https://prove2.me/theorems/d84b7e88-0709-44f1-a35c-ed9edb51d960
-- title:
--   Global Theory: topological Krull Dim preimage generic Point eq
-- statement:
--   The Global Theory construction uses the topological Krull Dim preimage generic Point eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L413-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L413-L449

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
attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem GlobalTheory.topologicalKrullDim_preimage_genericPoint_eq {d : ℕ}
    (hd : letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
      Algebra.trdeg O Y.functionField = d) :
    topologicalKrullDim (f ⁻¹' {genericPoint (Spec (.of O))} : Set Y) = d := by sorry
