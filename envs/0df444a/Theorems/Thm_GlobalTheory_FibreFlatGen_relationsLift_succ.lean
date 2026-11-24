-- Prove2me | Theorems.Thm_GlobalTheory_FibreFlatGen_relationsLift_succ
-- name    : GlobalTheory.FibreFlatGen.relationsLift_succ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:25:13.241536+00:00
-- url     : https://prove2.me/theorems/9aeb523b-2276-4414-b214-7a00957aa850
-- title:
--   Fibre Flat Gen: relations Lift succ
-- statement:
--   The Fibre Flat Gen construction uses the relations Lift succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RTensorInjectiveOfFlatBaseChange.lean#L65-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RTensorInjectiveOfFlatBaseChange.lean#L65-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RTensorInjectiveOfFlatBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory GlobalTheory.FibreFlatGen
open LocalFlat
universe u

theorem GlobalTheory.FibreFlatGen.relationsLift_succ {R : Type*} {A : Type u} {M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Flat R M] (J : Ideal R) (k : ℕ)
    (hinj : ∀ (N' N : Type u) [AddCommGroup N'] [AddCommGroup N]
      [Module (A ⧸ J.map (algebraMap R A)) N'] [Module (A ⧸ J.map (algebraMap R A)) N]
      [Module A N'] [Module A N] [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N']
      [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N]
      (ι : N' →ₗ[A ⧸ J.map (algebraMap R A)] N), Function.Injective ι →
        Function.Injective ((ι.restrictScalars A).lTensor M))
    (h : RelationsLift (J.map (algebraMap R A) ^ k) M) :
    RelationsLift (J.map (algebraMap R A) ^ (k + 1)) M := by sorry
