-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_altSt
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.altSt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:17.834722+00:00
-- url     : https://prove2.me/theorems/e07762ef-918b-4ebe-9504-d233c6a17387
-- title:
--   Hodge Alt: alt St
-- statement:
--   The Hodge Alt construction uses the alt St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L459-L493
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L459-L493

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt

theorem GlobalTheory.CompanionTheory.HodgeAlt.altSt : OneFormCohSt → TwoFormCohSt → AltSt := by sorry
