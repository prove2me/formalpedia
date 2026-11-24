-- Prove2me | Theorems.Thm_GlobalTheory_krullAkizuki_of_birational
-- name    : GlobalTheory.krullAkizuki_of_birational
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:15.51821+00:00
-- url     : https://prove2.me/theorems/05d32f7a-97a8-4ef8-86fd-1483a7bff177
-- title:
--   Global Theory: krull Akizuki of birational
-- statement:
--   The Global Theory construction uses the krull Akizuki of birational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L121-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L121-L160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
variable [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]

theorem GlobalTheory.krullAkizuki_of_birational
    (hB : ∀ x : B, ∃ c : A, c ≠ 0 ∧ ∃ b : A, algebraMap A B c * x = algebraMap A B b) :
    IsNoetherianRing B ∧ Ring.DimensionLEOne B := by sorry
