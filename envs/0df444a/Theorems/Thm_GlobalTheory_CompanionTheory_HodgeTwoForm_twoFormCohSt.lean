-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_twoFormCohSt
-- name    : GlobalTheory.CompanionTheory.HodgeTwoForm.twoFormCohSt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:23.296664+00:00
-- url     : https://prove2.me/theorems/b9fd0886-f5d0-540d-8c77-d46e56927036
-- title:
--   Hodge Two Form: two Form Coh St
-- statement:
--   The Hodge Two Form construction uses the two Form Coh St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L186-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L186-L232

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm

theorem GlobalTheory.CompanionTheory.HodgeTwoForm.twoFormCohSt : TwoFormCohSt := by sorry
