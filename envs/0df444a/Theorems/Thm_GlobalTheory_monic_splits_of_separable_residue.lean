-- Prove2me | Theorems.Thm_GlobalTheory_monic_splits_of_separable_residue
-- name    : GlobalTheory.monic_splits_of_separable_residue
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:11:09.200832+00:00
-- url     : https://prove2.me/theorems/843ccc9f-d562-4186-a1f2-d1688fff5397
-- title:
--   Global Theory: monic splits of separable residue
-- statement:
--   The Global Theory construction uses the monic splits of separable residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonicSplitsValuationSubringOfSeparableReduction.lean#L6-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonicSplitsValuationSubringOfSeparableReduction.lean#L6-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicSplitsValuationSubringOfSeparableReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
open GlobalTheory

theorem GlobalTheory.monic_splits_of_separable_residue (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (V : ValuationSubring Ω) (q : Polynomial V) (hq : q.Monic)
    (hs : (q.map (IsLocalRing.residue V)).Separable) :
    ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by sorry
