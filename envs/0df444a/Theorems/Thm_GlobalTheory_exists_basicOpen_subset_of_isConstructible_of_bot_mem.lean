-- Prove2me | Theorems.Thm_GlobalTheory_exists_basicOpen_subset_of_isConstructible_of_bot_mem
-- name    : GlobalTheory.exists_basicOpen_subset_of_isConstructible_of_bot_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:46.948888+00:00
-- url     : https://prove2.me/theorems/99c847ab-3d8f-4b9f-ab80-71723c5b6d97
-- title:
--   Global Theory: exists basic Open subset of is Constructible of bot mem
-- statement:
--   The Global Theory construction uses the exists basic Open subset of is Constructible of bot mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroForallComplexPointExtend.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroForallComplexPointExtend.lean#L8-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroForallComplexPointExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_basicOpen_subset_of_isConstructible_of_bot_mem {B : Type*} [CommRing B] [IsDomain B]
    {s : Set (PrimeSpectrum B)} (hs : Topology.IsConstructible s)
    (h0 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ s) :
    ∃ q : B, q ≠ 0 ∧ ∀ p : PrimeSpectrum B, q ∉ p.asIdeal → p ∈ s := by sorry
