-- Prove2me | Theorems.Thm_GlobalTheory_exists_isDiscreteValuationRing_of_unramified
-- name    : GlobalTheory.exists_isDiscreteValuationRing_of_unramified
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:05.696652+00:00
-- url     : https://prove2.me/theorems/ad3465a9-ed69-40b6-94a5-10d0c0b44dab
-- title:
--   Global Theory: exists is Discrete Valuation Ring of unramified
-- statement:
--   The Global Theory construction uses the exists is Discrete Valuation Ring of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L378-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L378-L383

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem GlobalTheory.exists_isDiscreteValuationRing_of_unramified (B : Type*) [CommRing B] [IsLocalRing B]
    [Algebra V B] [IsLocalHom (algebraMap V B)] [Module.Flat V B] [Algebra.EssFiniteType V B]
    [Algebra.FormallyUnramified V B] : ∃ _ : IsDomain B, IsDiscreteValuationRing B := by sorry
