-- Prove2me | Theorems.Thm_GlobalTheory_exists_isDiscreteValuationRing_of_flat
-- name    : GlobalTheory.exists_isDiscreteValuationRing_of_flat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:33.365796+00:00
-- url     : https://prove2.me/theorems/13824421-f987-44fb-938e-ec7aa8a949e5
-- title:
--   Global Theory: exists is Discrete Valuation Ring of flat
-- statement:
--   The Global Theory construction uses the exists is Discrete Valuation Ring of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L365-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L365-L376

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

theorem GlobalTheory.exists_isDiscreteValuationRing_of_flat (B : Type*) [CommRing B] [IsLocalRing B]
    [Algebra V B] [Module.Flat V B]
    (hm : (maximalIdeal V).map (algebraMap V B) = maximalIdeal B)
    (hs : ⨅ n : ℕ, maximalIdeal B ^ n = ⊥) : ∃ _ : IsDomain B, IsDiscreteValuationRing B := by sorry
