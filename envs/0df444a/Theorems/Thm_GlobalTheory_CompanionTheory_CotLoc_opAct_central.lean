-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_opAct_central
-- name    : GlobalTheory.CompanionTheory.CotLoc.opAct_central
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:37.062935+00:00
-- url     : https://prove2.me/theorems/46c81ce8-39a3-567f-ba16-70c09e40f73a
-- title:
--   Cot Loc: op Act central
-- statement:
--   The Cot Loc construction uses the op Act central property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L212-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L212-L216

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc

theorem GlobalTheory.CompanionTheory.CotLoc.opAct_central (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] :
    letI := opAct B M
    IsCentralScalar B M := by sorry
