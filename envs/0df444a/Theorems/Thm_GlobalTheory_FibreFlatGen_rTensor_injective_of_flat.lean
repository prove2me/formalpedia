-- Prove2me | Theorems.Thm_GlobalTheory_FibreFlatGen_rTensor_injective_of_flat
-- name    : GlobalTheory.FibreFlatGen.rTensor_injective_of_flat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:23.142791+00:00
-- url     : https://prove2.me/theorems/b5da4db6-e329-4c2f-b4ea-4ef0db0d0e4f
-- title:
--   Fibre Flat Gen: r Tensor injective of flat
-- statement:
--   The Fibre Flat Gen construction uses the r Tensor injective of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RTensorInjectiveOfFlatBaseChange.lean#L38-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RTensorInjectiveOfFlatBaseChange.lean#L38-L63

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

theorem GlobalTheory.FibreFlatGen.rTensor_injective_of_flat {A B L N' N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup L] [Module A L] [Module B L] [IsScalarTower A B L] [Module.Flat B L]
    [AddCommGroup N'] [AddCommGroup N] [Module A N'] [Module A N] (ι : N' →ₗ[A] N)
    (hι : Function.Injective (ι.rTensor B)) : Function.Injective (ι.lTensor L) := by sorry
