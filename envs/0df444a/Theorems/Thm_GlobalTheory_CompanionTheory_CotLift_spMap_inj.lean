-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_spMap_inj
-- name    : GlobalTheory.CompanionTheory.CotLift.spMap_inj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:56.64381+00:00
-- url     : https://prove2.me/theorems/42873f38-d0ab-43a2-8329-1f8fbd0f9784
-- title:
--   Cot Lift: sp Map inj
-- statement:
--   The Cot Lift construction uses the sp Map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZero.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZero.lean#L17-L19

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZero
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLift

theorem GlobalTheory.CompanionTheory.CotLift.spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by sorry
