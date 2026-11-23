-- Prove2me | Theorems.Thm_GlobalTheory_exists_affine_chart_trdeg_eq
-- name    : GlobalTheory.exists_affine_chart_trdeg_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:18.056069+00:00
-- url     : https://prove2.me/theorems/61ee2545-8d4c-48a6-95c9-03d14d154b05
-- title:
--   Global Theory: exists affine chart trdeg eq
-- statement:
--   The Global Theory construction uses the exists affine chart trdeg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L367-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L367-L400

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
open AlgebraicGeometry CategoryTheory Topology
variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]

theorem GlobalTheory.exists_affine_chart_trdeg_eq (x : Y) :
    letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra O A)
      (_ : Algebra.FiniteType O A) (_ : FaithfulSMul O A) (j : Spec (.of A) ⟶ Y)
      (_ : IsOpenImmersion j), x ∈ Set.range j ∧
      j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A)) ∧
      Algebra.trdeg O A = Algebra.trdeg O Y.functionField := by sorry
