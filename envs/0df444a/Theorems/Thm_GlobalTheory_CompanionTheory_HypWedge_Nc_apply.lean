-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_Nc_apply
-- name    : GlobalTheory.CompanionTheory.HypWedge.Nc_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:47.730884+00:00
-- url     : https://prove2.me/theorems/3499a02f-a7ef-5404-9657-ed86c5bb2bc8
-- title:
--   Hyp Wedge: Nc apply
-- statement:
--   The Hyp Wedge construction uses the Nc apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L166-L168

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
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HypWedge.Nc_apply (hcl : Closed1 F = ⊤) (a b : Glob1 F) :
    Nc hcl (exteriorPower.ιMulti R 2 ![a, b]) = cupZZ F (cl hcl a) (cl hcl b) := by sorry
