-- Prove2me | Theorems.Thm_GlobalTheory_isAlgebraic_of_flat_of_formallyUnramified
-- name    : GlobalTheory.isAlgebraic_of_flat_of_formallyUnramified
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:15.686541+00:00
-- url     : https://prove2.me/theorems/60b29975-bf42-4bf5-bbc2-4fc358879a9c
-- title:
--   Global Theory: is Algebraic of flat of formally Unramified
-- statement:
--   The Global Theory construction uses the is Algebraic of flat of formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ValuationRingOfFlatOfFormallyUnramified.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ValuationRingOfFlatOfFormallyUnramified.lean#L25-L35

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

theorem GlobalTheory.isAlgebraic_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W]
    [CommRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : Algebra.IsAlgebraic W B := by sorry
