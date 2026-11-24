-- Prove2me | Theorems.Thm_GlobalTheory_Ex_summable_vt_QT
-- name    : GlobalTheory.Ex.summable_vt_QT
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:38.2108+00:00
-- url     : https://prove2.me/theorems/2a50858b-4907-4ef8-baec-34c3c9026122
-- title:
--   Ex: summable vt QT
-- statement:
--   The Ex construction uses the summable vt QT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SummableVtQT.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SummableVtQT.lean#L48-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SummableVtQT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex

theorem GlobalTheory.Ex.summable_vt_QT : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) := by sorry
