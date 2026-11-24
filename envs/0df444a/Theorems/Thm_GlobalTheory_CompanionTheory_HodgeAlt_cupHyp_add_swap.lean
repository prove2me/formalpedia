-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_cupHyp_add_swap
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.cupHyp_add_swap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:04.295419+00:00
-- url     : https://prove2.me/theorems/e66fdb01-0b12-4f98-b65b-e26498c0ada7
-- title:
--   Hodge Alt: cup Hyp add swap
-- statement:
--   The Hodge Alt construction uses the cup Hyp add swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L18-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L18-L35

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
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem GlobalTheory.CompanionTheory.HodgeAlt.cupHyp_add_swap (a b : Hyp1 F) : cupHyp F a b + cupHyp F b a = 0 := by sorry
