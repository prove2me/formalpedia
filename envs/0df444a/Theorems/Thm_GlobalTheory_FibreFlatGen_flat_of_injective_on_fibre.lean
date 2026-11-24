-- Prove2me | Theorems.Thm_GlobalTheory_FibreFlatGen_flat_of_injective_on_fibre
-- name    : GlobalTheory.FibreFlatGen.flat_of_injective_on_fibre
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:27.94827+00:00
-- url     : https://prove2.me/theorems/002a8284-0dd0-46b3-a4b8-3565bd0f718a
-- title:
--   Fibre Flat Gen: flat of injective on fibre
-- statement:
--   The Fibre Flat Gen construction uses the flat of injective on fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RTensorInjectiveOfFlatBaseChange.lean#L145-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RTensorInjectiveOfFlatBaseChange.lean#L145-L161

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

theorem GlobalTheory.FibreFlatGen.flat_of_injective_on_fibre {R : Type*} {A : Type u} {L : Type*} [CommRing R] [CommRing A]
    [CommRing L] [Algebra R A] [Algebra A L] [Algebra R L] [IsScalarTower R A L]
    [IsNoetherianRing A] [IsNoetherianRing L] [Module.Flat R L] (J : Ideal R)
    (hJ : (J.map (algebraMap R A)).map (algebraMap A L) ≤ Ideal.jacobson ⊥)
    (hinj : ∀ (N' N : Type u) [AddCommGroup N'] [AddCommGroup N]
      [Module (A ⧸ J.map (algebraMap R A)) N'] [Module (A ⧸ J.map (algebraMap R A)) N]
      [Module A N'] [Module A N] [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N']
      [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N]
      (ι : N' →ₗ[A ⧸ J.map (algebraMap R A)] N), Function.Injective ι →
        Function.Injective ((ι.restrictScalars A).lTensor L)) :
    Module.Flat A L := by sorry
