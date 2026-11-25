-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_inj_N
-- name    : GlobalTheory.CompanionTheory.HypWedge.inj_N
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:55.226431+00:00
-- url     : https://prove2.me/theorems/15fd7afe-cf3c-4e02-b4cf-9d40d0b041f7
-- title:
--   Hyp Wedge: inj N
-- statement:
--   The Hyp Wedge construction uses the inj N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L293-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L293-L310

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO

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
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HypWedge.inj_N (hs : Function.Surjective (toO F)) (hcl : Closed1 F = ⊤) (c : Tot1 F) (w : W0 F 2)
    (hc : dTot1 F c = (0, 0, w)) : w = 0 := by sorry
