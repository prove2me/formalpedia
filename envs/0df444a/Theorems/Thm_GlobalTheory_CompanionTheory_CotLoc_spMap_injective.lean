-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_spMap_injective
-- name    : GlobalTheory.CompanionTheory.CotLoc.spMap_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:53:59.64946+00:00
-- url     : https://prove2.me/theorems/61ee8c14-2af2-4022-95a6-32890bfdd822
-- title:
--   Cot Loc: sp Map injective
-- statement:
--   The Cot Loc construction uses the sp Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L12-L15

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

theorem GlobalTheory.CompanionTheory.CotLoc.spMap_injective {a b : Type} [CommRing a] [CommRing b] {f g : a →+* b}
    (h : spMap f = spMap g) : f = g := by sorry
