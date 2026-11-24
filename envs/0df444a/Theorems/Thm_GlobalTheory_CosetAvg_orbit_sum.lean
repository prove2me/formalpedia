-- Prove2me | Theorems.Thm_GlobalTheory_CosetAvg_orbit_sum
-- name    : GlobalTheory.CosetAvg.orbit_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:47.758075+00:00
-- url     : https://prove2.me/theorems/70464e64-0ff0-4a89-af42-9b9ebf81370a
-- title:
--   Coset Avg: orbit sum
-- statement:
--   The Coset Avg construction uses the orbit sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumTranslatesEqDoubleCosetAverage.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumTranslatesEqDoubleCosetAverage.lean#L8-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTranslatesEqDoubleCosetAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.CosetAvg
open MulAction

theorem GlobalTheory.CosetAvg.orbit_sum {H X M : Type*} [Group H] [Fintype H] [MulAction H X] [AddCommGroup M]
    [Module ℂ M] (y : X) [Fintype (orbit H y)] (F : X → M) :
    (Fintype.card (orbit H y) : ℂ) • ∑ h : H, F (h • y) =
      (Fintype.card H : ℂ) • ∑ z : orbit H y, F z := by sorry
