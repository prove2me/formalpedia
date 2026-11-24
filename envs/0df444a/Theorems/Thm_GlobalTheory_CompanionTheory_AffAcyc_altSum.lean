-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_altSum
-- name    : GlobalTheory.CompanionTheory.AffAcyc.altSum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:25:59.443826+00:00
-- url     : https://prove2.me/theorems/b8d8a2bd-e8cb-4f6d-9887-f1c4b0006b5b
-- title:
--   Aff Acyc: alt Sum
-- statement:
--   The Aff Acyc construction uses the alt Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L38-L45

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc

theorem GlobalTheory.CompanionTheory.AffAcyc.altSum {R : Type} [CommRing R] (m : ℕ) :
    2 * (∑ i : Fin m, (-1 : R) ^ (i : ℕ)) + (-1) ^ m = 1 := by sorry
