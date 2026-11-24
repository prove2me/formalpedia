-- Prove2me | Theorems.Thm_GlobalTheory_isArtinianRing_quotient_of_dimensionLEOne
-- name    : GlobalTheory.isArtinianRing_quotient_of_dimensionLEOne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:03.932604+00:00
-- url     : https://prove2.me/theorems/90fb9fd3-3e14-43fd-b70d-40aa78a4323c
-- title:
--   Global Theory: is Artinian Ring quotient of dimension LEOne
-- statement:
--   The Global Theory construction uses the is Artinian Ring quotient of dimension LEOne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L11-L26

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

theorem GlobalTheory.isArtinianRing_quotient_of_dimensionLEOne {I : Ideal A} (hI : I ≠ ⊥) :
    IsArtinianRing (A ⧸ I) := by sorry
