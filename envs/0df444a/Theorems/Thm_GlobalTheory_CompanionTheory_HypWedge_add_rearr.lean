-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_add_rearr
-- name    : GlobalTheory.CompanionTheory.HypWedge.add_rearr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:37.937773+00:00
-- url     : https://prove2.me/theorems/34df3b10-1daa-4b06-b1f6-e992833df88d
-- title:
--   Hyp Wedge: add rearr
-- statement:
--   The Hyp Wedge construction uses the add rearr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L245-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L245-L246

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge

theorem GlobalTheory.CompanionTheory.HypWedge.add_rearr {A : Type} [AddCommGroup A] (a b l d : A) : a = a - b - l - d + l + b + d := by sorry
