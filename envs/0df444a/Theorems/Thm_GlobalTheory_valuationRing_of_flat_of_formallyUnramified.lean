-- Prove2me | Theorems.Thm_GlobalTheory_valuationRing_of_flat_of_formallyUnramified
-- name    : GlobalTheory.valuationRing_of_flat_of_formallyUnramified
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:24:41.690629+00:00
-- url     : https://prove2.me/theorems/2fe7940d-7acf-49de-b8b4-adab71e0ef67
-- title:
--   Global Theory: valuation Ring of flat of formally Unramified
-- statement:
--   The Global Theory construction uses the valuation Ring of flat of formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ValuationRingOfFlatOfFormallyUnramified.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ValuationRingOfFlatOfFormallyUnramified.lean#L37-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.valuationRing_of_flat_of_formallyUnramified :
    ∀ (W B : Type) [CommRing W] [IsDomain W] [ValuationRing W] [CommRing B] [IsDomain B]
      [IsLocalRing B] [Algebra W B] [Module.Flat W B] [Algebra.EssFiniteType W B]
      [Algebra.FormallyUnramified W B], ValuationRing B ∧ Algebra.IsAlgebraic W B := by sorry
