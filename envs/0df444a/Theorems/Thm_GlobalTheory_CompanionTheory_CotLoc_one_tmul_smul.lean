-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_one_tmul_smul
-- name    : GlobalTheory.CompanionTheory.CotLoc.one_tmul_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:06:15.646117+00:00
-- url     : https://prove2.me/theorems/1b945f2c-064d-5a43-b6d3-b3e8589418c8
-- title:
--   Cot Loc: one tmul smul
-- statement:
--   The Cot Loc construction uses the one tmul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L236-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L236-L240

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

theorem GlobalTheory.CompanionTheory.CotLoc.one_tmul_smul {R' A P : Type} [CommRing R'] [CommRing A] [Algebra A R'] [AddCommGroup P]
    [Module A P] (a : A) (x : P) :
    (1 : R') ⊗ₜ[A] (a • x) = algebraMap A R' a • ((1 : R') ⊗ₜ[A] x) := by sorry
