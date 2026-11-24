-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_prim_cup
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.prim_cup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:25:51.230241+00:00
-- url     : https://prove2.me/theorems/b30a09dd-25cc-4c01-8934-1027aa5648e4
-- title:
--   Hodge Alt: prim cup
-- statement:
--   The Hodge Alt construction uses the prim cup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L306-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L306-L311

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
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HodgeAlt.prim_cup (m p q : CoefMap (RingHom.id R) F G)
    (hm : ∀ c, pullHyp1 m c = pullHyp1 p c + pullHyp1 q c) (c : Hyp1 F) :
    pullHyp2 m (cupHyp F c c) = pullHyp2 p (cupHyp F c c) + pullHyp2 q (cupHyp F c c) := by sorry
