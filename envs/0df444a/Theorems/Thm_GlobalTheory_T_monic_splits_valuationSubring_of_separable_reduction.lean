-- Prove2me | Theorems.Thm_GlobalTheory_T_monic_splits_valuationSubring_of_separable_reduction
-- name    : GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:31.430642+00:00
-- url     : https://prove2.me/theorems/fc8941e7-0740-4a43-9d92-e2ddfd85df9d
-- title:
--   T: monic splits valuation Subring of separable reduction
-- statement:
--   The T construction uses the monic splits valuation Subring of separable reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonicSplitsValuationSubringOfSeparableReductionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonicSplitsValuationSubringOfSeparableReductionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicSplitsValuationSubringOfSeparableReduction
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicSplitsValuationSubringOfSeparableReductionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω] (V : ValuationSubring Ω) (q : Polynomial V), q.Monic → (q.map (IsLocalRing.residue V)).Separable → ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by sorry
