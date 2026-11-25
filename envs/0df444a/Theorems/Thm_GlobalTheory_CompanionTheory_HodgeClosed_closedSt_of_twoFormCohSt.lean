-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeClosed_closedSt_of_twoFormCohSt
-- name    : GlobalTheory.CompanionTheory.HodgeClosed.closedSt_of_twoFormCohSt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:50.446364+00:00
-- url     : https://prove2.me/theorems/634d6f65-70d1-4260-9eb5-28ff6ca5e76e
-- title:
--   Hodge Closed: closed St of two Form Coh St
-- statement:
--   The Hodge Closed construction uses the closed St of two Form Coh St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedStOfTwoFormCohSt.lean#L89-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedStOfTwoFormCohSt.lean#L89-L122

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedStOfTwoFormCohSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeClosed

theorem GlobalTheory.CompanionTheory.HodgeClosed.closedSt_of_twoFormCohSt : TwoFormCohSt → ClosedSt := by sorry
