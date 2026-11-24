-- Prove2me | Theorems.Thm_GlobalTheory_FibreFlatGen_lTensor_injective_of_fibre
-- name    : GlobalTheory.FibreFlatGen.lTensor_injective_of_fibre
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:48.26895+00:00
-- url     : https://prove2.me/theorems/bfde81ee-751a-45c7-91d5-a01011d16a25
-- title:
--   Fibre Flat Gen: l Tensor injective of fibre
-- statement:
--   The Fibre Flat Gen construction uses the l Tensor injective of fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RTensorInjectiveOfFlatBaseChange.lean#L163-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RTensorInjectiveOfFlatBaseChange.lean#L163-L201

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

theorem GlobalTheory.FibreFlatGen.lTensor_injective_of_fibre {A B A' L C N' N : Type} [CommRing A] [CommRing B] [CommRing A']
    [CommRing L] [CommRing C] [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    [Algebra A A'] (S : Submonoid A) [IsLocalization S A'] [Algebra A' L] [IsScalarTower A A' L]
    [Algebra A' C] [Algebra A C] [IsScalarTower A A' C]
    [Module.Flat B L] [Module.Flat C (C ⊗[A] B)]
    [AddCommGroup N'] [AddCommGroup N] [Module C N'] [Module C N] [Module A' N'] [Module A' N]
    [IsScalarTower A' C N'] [IsScalarTower A' C N] (ι : N' →ₗ[C] N) (hι : Function.Injective ι) :
    Function.Injective ((ι.restrictScalars A').lTensor L) := by sorry
