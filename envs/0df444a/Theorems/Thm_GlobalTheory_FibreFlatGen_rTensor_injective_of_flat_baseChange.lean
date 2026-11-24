-- Prove2me | Theorems.Thm_GlobalTheory_FibreFlatGen_rTensor_injective_of_flat_baseChange
-- name    : GlobalTheory.FibreFlatGen.rTensor_injective_of_flat_baseChange
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:28.944325+00:00
-- url     : https://prove2.me/theorems/50a1e947-0a22-4953-87ed-632416efd7a5
-- title:
--   Fibre Flat Gen: r Tensor injective of flat base Change
-- statement:
--   The Fibre Flat Gen construction uses the r Tensor injective of flat base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RTensorInjectiveOfFlatBaseChange.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RTensorInjectiveOfFlatBaseChange.lean#L13-L36

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

theorem GlobalTheory.FibreFlatGen.rTensor_injective_of_flat_baseChange {A C B N' N : Type*} [CommRing A] [CommRing C]
    [Algebra A C] [AddCommGroup B] [Module A B] [Module.Flat C (C ⊗[A] B)]
    [AddCommGroup N'] [AddCommGroup N] [Module C N'] [Module C N] [Module A N'] [Module A N]
    [IsScalarTower A C N'] [IsScalarTower A C N] (ι : N' →ₗ[C] N) (hι : Function.Injective ι) :
    Function.Injective ((ι.restrictScalars A).rTensor B) := by sorry
