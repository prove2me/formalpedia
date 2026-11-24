-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wb_apply
-- name    : GlobalTheory.CompanionTheory.HodgeTwoForm.wb_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:24:07.816493+00:00
-- url     : https://prove2.me/theorems/31358c32-b99e-4831-8e40-6281838cea75
-- title:
--   Hodge Two Form: wb apply
-- statement:
--   The Hodge Two Form construction uses the wb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L48-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L48-L48

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
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}

theorem GlobalTheory.CompanionTheory.HodgeTwoForm.wb_apply (a b : M) : wb (A := A) a b = exteriorPower.ιMulti A 2 ![a, b] := by sorry
